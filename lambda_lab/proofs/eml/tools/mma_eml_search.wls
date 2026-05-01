#!/usr/bin/env wolframscript
(* mma_eml_search.wls — exhaustive symbolic search for an EMLTerm
   matching a target expression.

   Usage:  wolframscript -file mma_eml_search.wls <input.json>
*)

$RecursionLimit = 4096;
$IterationLimit = 1000000;

inputPath = If[Length[$ScriptCommandLine] >= 2, $ScriptCommandLine[[2]], "/dev/stdin"];

(* Mathematica's "JSON" import returns a list of String -> _ rules. *)
specRaw = Import[inputPath, "JSON"];
specGet[k_] := k /. specRaw;

target = ToExpression[specGet["target"]];
varStrs = specGet["vars"];                                (* list of strings *)
varSyms = ToExpression /@ varStrs;                        (* list of symbols *)
constraint = With[{c = specGet["constraint"]},
  If[c === Null || c === "" || c === "constraint", True, ToExpression[c]]];
maxSize = specGet["max_size"];

(* EML operator *)
eml[a_, b_] := Exp[a] - Log[b];

(* leafSymbols: list of {leanForm, mathValue} for each atom available. *)
varLeanForm[s_String] := Switch[s, "x", ".var", "y", ".varY", _, ".var" <> s];
leafSymbols = Join[{{".one", 1}},
  MapThread[{varLeanForm[#1], #2} &, {varStrs, varSyms}]];

(* Iterative tree generator: build all trees of size 1..maxSize.
   Only odd sizes are reachable (1 leaf, or 1 internal node + odd+odd). *)
allTrees = <||>;
allTrees[1] = leafSymbols;
Do[
  allTrees[n] = Flatten[
    Table[
      Module[{lefts = Lookup[allTrees, k, {}], rights = Lookup[allTrees, n - 1 - k, {}]},
        Table[
          {".eml (" <> l[[1]] <> ") (" <> r[[1]] <> ")",
           eml[l[[2]], r[[2]]]},
          {l, lefts}, {r, rights}
        ]
      ],
      {k, 1, n - 2, 2}
    ],
    2
  ],
  {n, 3, maxSize, 2}
];

(* Match check: true iff candidate evaluates to target under constraint. *)
matchesTarget[candidateValue_] := Module[{diff},
  diff = candidateValue - target;
  Which[
    Simplify[diff, constraint] === 0, True,
    FullSimplify[diff, constraint, TimeConstraint -> 5] === 0, True,
    FullSimplify[PowerExpand[diff], constraint, TimeConstraint -> 5] === 0, True,
    True, False
  ]
];

(* Search by ascending size. *)
searchedCount = 0;
result = Catch[
  Do[
    If[KeyExistsQ[allTrees, size],
      Module[{candidates = allTrees[size]},
        WriteString["stderr",
          "size " <> ToString[size] <> ": " <>
          ToString[Length[candidates]] <> " trees\n"];
        Do[
          searchedCount = searchedCount + 1;
          If[matchesTarget[candidates[[i, 2]]],
            Throw[<|"size" -> size,
                    "tree" -> candidates[[i, 1]],
                    "value" -> candidates[[i, 2]]|>]
          ],
          {i, Length[candidates]}
        ]
      ]
    ],
    {size, 1, maxSize, 2}
  ];
  Missing[]
];

output = If[result === Missing[],
  <|"ok" -> False, "reason" -> "no match up to size " <> ToString[maxSize],
    "searched" -> searchedCount|>,
  <|"ok" -> True, "size" -> result["size"], "tree" -> result["tree"],
    "value" -> ToString[result["value"], InputForm],
    "searched" -> searchedCount|>
];

WriteString["stdout", ExportString[output, "JSON"]];
