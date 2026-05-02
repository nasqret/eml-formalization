#!/usr/bin/env wolframscript
(* mma_eml_search_v2.wls - numerical-prefilter EML term search.

   The v1 script worked by enumerating every binary tree and feeding each
   to FullSimplify.  That scaled poorly: FullSimplify was the bottleneck
   and recomputed the same sub-expressions many times.

   v2 design:

     1. Pick K transcendentally-independent numerical points (here K=6
        with WorkingPrecision 30, drawn from a seeded RNG).
     2. Each tree carries a *numerical signature* = K-tuple of evaluations
        at the sample points.  Crucially, signatures compose dynamically:
        sig(eml(L, R)) = Exp[sig(L)] - Log[sig(R)] componentwise.
        So we never re-evaluate sub-expressions from scratch.
     3. A signature->representative `Association` keeps one tree per
        distinct signature (rounded to 12 decimals).
     4. Only candidates whose signature matches the target's signature
        (componentwise abs-diff < 10^-6) are sent to symbolic verification,
        guarded by `TimeConstrained[..., 10]`.
     5. Iterative deepening over odd sizes 1, 3, 5, ... up to max_size.

   Output: JSON document with ok:true|false plus diagnostic counters.

   Spec extension: an optional "domain" key with value "complex" switches
   numerical evaluation from real to complex (used by the chunk for `i`).

   Usage:  wolframscript -file mma_eml_search_v2.wls <input.json>
*)

$RecursionLimit = 8192;
$IterationLimit = 1000000;
SeedRandom[20260427];

(* Silence numerically harmless precision/underflow warnings that would
   otherwise contaminate our JSON stdout, and route remaining messages
   to stderr so the JSON output is clean. *)
Off[General::munfl];
Off[General::ovfl];
Off[General::unfl];
Off[General::pnois];
Off[General::infy];
Off[General::indet];
Off[Power::infy];
Off[N::meprec];
Off[Round::tolnnf];
$Messages = {Streams["stderr"]};

inputPath = If[Length[$ScriptCommandLine] >= 2, $ScriptCommandLine[[2]], "/dev/stdin"];

specRaw = Import[inputPath, "JSON"];
specGet[k_] := k /. specRaw;
specGetDef[k_, default_] := With[{v = k /. specRaw}, If[v === k, default, v]];

target     = ToExpression[specGet["target"]];
varStrs    = specGet["vars"];
varSyms    = ToExpression /@ varStrs;
constraint = With[{c = specGet["constraint"]},
  If[c === Null || c === "" || c === "constraint", True, ToExpression[c]]];
maxSize    = specGet["max_size"];
domain     = ToLowerCase @ ToString @ specGetDef["domain", "real"];

isComplex = (domain === "complex");

(* EML operator: Exp[a] - Log[b].  Mathematica's Log uses the principal
   branch on negatives, so for the complex case Log[-1] = I*Pi natively. *)
eml[a_, b_] := Exp[a] - Log[b];

(* --- Numerical sample points --------------------------------------- *)
wprec = 22;       (* MachinePrecision-friendly band; high enough to
                     dedup but cheap to compute *)
numSigPts = 6;

(* Build sample points.  For empty-vars cases we still need K *distinct*
   sample points, but with no free vars there is nothing to vary, so all
   K signature values for any single tree are identical.  In that case
   we collapse to a single point and rely on the symbolic check.    *)
makeSigPts[vs_] :=
  If[Length[vs] === 0,
    {{}},
    Module[{base},
      base = If[Length[vs] === 1,
        (* spread along a fixed grid *)
        {{0.31`22}, {0.97`22}, {1.7`22}, {2.41`22}, {2.93`22}, {3.41`22}},
        Table[
          Table[N[RandomReal[{0.31, 3.71}], wprec], {Length[vs]}],
          numSigPts]
      ];
      base
    ]
  ];

sigPts = makeSigPts[varSyms];

(* Numerically evaluate `expr` at each sample point, returning a list. *)
sigOfSym[expr_] :=
  Map[
    Function[pt,
      Quiet @ N[
        If[Length[varSyms] === 0, expr, expr /. Thread[varSyms -> pt]],
        wprec
      ]
    ],
    sigPts
  ];

(* Magnitude beyond which signatures are treated as numerically saturated.
   Any tree whose sig grows past this is dropped from the search front.    *)
sigMagCap = 10.^12;

isFiniteSig[s_] := And[
  Head[s] === List,
  FreeQ[s, Indeterminate | ComplexInfinity | DirectedInfinity[_]
            | Overflow | Overflow[] | Underflow | Underflow[] | $Failed],
  AllTrue[Flatten[s], NumericQ],
  AllTrue[Flatten[s], (Abs[#] < sigMagCap) &]
];

(* Compose two signatures: eml(L, R) -> Exp[L] - Log[R] componentwise.
   Numerical only; returns $Failed on any non-finite component or on
   any component whose magnitude exceeds sigMagCap (avoids Exp blowup). *)
combineSigs[sl_List, sr_List] := Module[{out},
  out = Quiet @ MapThread[(Exp[#1] - Log[#2]) &, {sl, sr}];
  If[isFiniteSig[out], out, $Failed]
];

targetSig = sigOfSym[target];

If[!isFiniteSig[targetSig],
  WriteString["stderr",
    "WARNING: target signature has singularities/non-numeric components.\n"];
];

WriteString["stderr",
  "[v2] target=" <> ToString[target, InputForm]
    <> " vars=" <> ToString[varStrs]
    <> " maxSize=" <> ToString[maxSize]
    <> " domain=" <> domain
    <> " sigPts=" <> ToString[Length[sigPts]] <> "\n"];

(* Compare numerical signatures at tolerance 10^-6. *)
sigMatchesTarget[s_] := Module[{diffs},
  diffs = Abs[s - targetSig];
  isFiniteSig[diffs] && Max[Re[diffs] + Im[diffs]] < 10.^-6
];

(* Signature key: round to 12 decimals.  Real & imag treated separately
   to keep complex-domain runs distinguishing. *)
sigKey[s_] := Map[
  Function[v, {Round[Re[v], 10.^-12], Round[Im[v], 10.^-12]}],
  s
];

(* --- Leaf set ------------------------------------------------------- *)
(* Each leaf is {leanForm, mmaForm, mmaValue}.  leanForm is the textual
   tree we will splat into Lean source.  mmaForm is the Mathematica-syntax
   string used to rebuild the symbolic value for FullSimplify (avoids
   parsing the Lean form which uses prefix function-call syntax).        *)
varLeanForm[v_String] := Switch[v, "x", ".var", "y", ".varY", _, ".var"];
leafs = Join[
  {{".one", "1", 1}},
  MapThread[{varLeanForm[#1], #1, #2} &, {varStrs, varSyms}]
];

(* --- Per-size dedup table ------------------------------------------ *)
(* sizeReps[n] = Association : sigKey -> {leanForm, mmaForm, sig} *)
sizeReps = <||>;

initLeafReps[] := Module[{out = <||>, sg, k},
  Do[
    sg = sigOfSym[leafs[[i, 3]]];
    If[isFiniteSig[sg],
      k = sigKey[sg];
      If[!KeyExistsQ[out, k],
        out[k] = {leafs[[i, 1]], leafs[[i, 2]], sg}];
    ],
    {i, Length[leafs]}];
  out
];

sizeReps[1] = initLeafReps[];

(* --- Search counters ----------------------------------------------- *)
totalGenerated   = 0;
totalUnique      = Length[sizeReps[1]];
numericMatches   = 0;
symbolicChecks   = 0;
foundResult      = None;

WriteString["stderr",
  "  size 1: leaf-reps " <> ToString[Length[sizeReps[1]]] <> "\n"];

(* --- Symbolic verification with bounded time ----------------------- *)
verifySymbolic[candidateValue_] := Module[{diff, ok},
  diff = candidateValue - target;
  ok = TimeConstrained[
    Module[{r1, r2},
      r1 = Simplify[diff, constraint];
      If[r1 === 0, Return[True, Module]];
      r2 = FullSimplify[diff, constraint];
      If[r2 === 0, Return[True, Module]];
      r2 = FullSimplify[PowerExpand[diff], constraint];
      r2 === 0
    ], 10, $TimedOut];
  ok === True
];

(* --- Build size-n table from sizes a (left) and (n-1-a) (right) ----
   Per rep we store {leanForm, mmaForm, sig}.  mmaForm is a string in
   Mathematica function-call syntax: "eml[L, R]"; we postpone calling
   ToExpression until a sig actually matches the target.                 *)
buildSize[n_] := Module[
  {result = <||>, lefts, rights, count = 0,
   sg, k, leanForm, mmaForm, lk, rk, l, r, sigCombined},
  Do[
    lefts  = Lookup[sizeReps, a, <||>];
    rights = Lookup[sizeReps, n - 1 - a, <||>];
    Do[
      l = lefts[lk];
      Do[
        r = rights[rk];
        count++;
        sigCombined = combineSigs[l[[3]], r[[3]]];
        If[sigCombined =!= $Failed,
          k = sigKey[sigCombined];
          If[!KeyExistsQ[result, k],
            leanForm = ".eml (" <> l[[1]] <> ") (" <> r[[1]] <> ")";
            mmaForm  = "eml[" <> l[[2]] <> ", " <> r[[2]] <> "]";
            result[k] = {leanForm, mmaForm, sigCombined};
          ];
        ];
        ,
        {rk, Keys[rights]}
      ],
      {lk, Keys[lefts]}
    ],
    {a, 1, n - 2, 2}
  ];
  {result, count}
];

(* Convert the stored Mathematica-form string into the symbolic value. *)
symValueFromMma[s_String] := ToExpression[s];

(* --- Iterative deepening ------------------------------------------- *)
result = Catch[
  Do[
    With[{kv = sizeReps[1][k]},
      If[sigMatchesTarget[kv[[3]]],
        numericMatches++;
        Module[{symVal = symValueFromMma[kv[[2]]]},
          symbolicChecks++;
          If[verifySymbolic[symVal],
            foundResult = <|"size" -> 1, "tree" -> kv[[1]],
                            "value" -> symVal|>;
            Throw[foundResult]
          ]
        ]
      ]
    ],
    {k, Keys[sizeReps[1]]}
  ];

  Do[
    Module[{built, raw, uniq, hits},
      built = buildSize[size];
      raw = built[[2]];
      sizeReps[size] = built[[1]];
      uniq = Length[built[[1]]];
      totalGenerated += raw;
      totalUnique += uniq;

      hits = 0;
      Do[
        With[{kv = sizeReps[size][k]},
          If[sigMatchesTarget[kv[[3]]],
            hits++;
            numericMatches++;
            Module[{symVal = symValueFromMma[kv[[2]]]},
              symbolicChecks++;
              If[verifySymbolic[symVal],
                foundResult = <|"size" -> size, "tree" -> kv[[1]],
                                "value" -> symVal|>;
                Throw[foundResult]
              ]
            ]
          ]
        ],
        {k, Keys[sizeReps[size]]}
      ];

      WriteString["stderr",
        "  size " <> ToString[size]
          <> ": raw=" <> ToString[raw]
          <> " uniq=" <> ToString[uniq]
          <> " numHits=" <> ToString[hits]
          <> " (cumUnique=" <> ToString[totalUnique] <> ")\n"];
    ],
    {size, 3, maxSize, 2}
  ];
  Missing[]
];

output = If[result === Missing[],
  <|"ok" -> False,
    "reason" -> "no match up to size " <> ToString[maxSize],
    "max_size" -> maxSize,
    "total_generated" -> totalGenerated,
    "total_unique_signatures" -> totalUnique,
    "numeric_matches" -> numericMatches,
    "symbolic_checks" -> symbolicChecks,
    "domain" -> domain|>,
  <|"ok" -> True,
    "size" -> result["size"],
    "tree" -> result["tree"],
    "value" -> ToString[result["value"], InputForm],
    "max_size" -> maxSize,
    "total_generated" -> totalGenerated,
    "total_unique_signatures" -> totalUnique,
    "numeric_matches" -> numericMatches,
    "symbolic_checks" -> symbolicChecks,
    "domain" -> domain|>
];

WriteString["stderr",
  "[v2] done: ok=" <> ToString[output["ok"]]
    <> " unique=" <> ToString[totalUnique]
    <> " numHits=" <> ToString[numericMatches]
    <> " symChecks=" <> ToString[symbolicChecks] <> "\n"];

WriteString["stdout", ExportString[output, "JSON"]];
