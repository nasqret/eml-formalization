"""Internacjonalizacja / Internationalization — Lambda Lab.

Two-language string dictionary. Default = ``pl``; ustawiane raz na sesję
(albo przez `LAMBDA_LAB_LANG=en`, albo komendą ``lang en`` w REPL).

Filozofia:
- klucze stringów są krótkie i opisowe (np. ``banner.tagline``),
- dla każdego klucza mamy parę PL/EN,
- jeśli któryś brakuje — fallback do PL,
- formatowanie via ``str.format``: ``t("hello", name="Bartek")``.

Persystencja: wybór języka zapisuje się w
``~/.local/share/lambda_lab/lang`` — drugi start REPL pamięta wybór.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import Any, Dict


SUPPORTED = ("pl", "en")


def _persist_path() -> Path:
    base = os.environ.get("XDG_DATA_HOME") or (Path.home() / ".local" / "share")
    return Path(base) / "lambda_lab" / "lang"


def _initial_lang() -> str:
    env = (os.environ.get("LAMBDA_LAB_LANG") or "").strip().lower()
    if env in SUPPORTED:
        return env
    saved = _persist_path()
    if saved.exists():
        try:
            val = saved.read_text(encoding="utf-8").strip().lower()
            if val in SUPPORTED:
                return val
        except OSError:
            pass
    return "pl"


_LANG = _initial_lang()


def get_lang() -> str:
    return _LANG


def set_lang(lang: str, persist: bool = True) -> bool:
    """Zmienia język sesji. Zwraca True jeśli udało się zmienić."""
    global _LANG
    lang = (lang or "").strip().lower()
    if lang not in SUPPORTED:
        return False
    _LANG = lang
    if persist:
        try:
            p = _persist_path()
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(lang + "\n", encoding="utf-8")
        except OSError:
            pass
    return True


# ---------------------------------------------------------------------------
# Słownik / Dictionary
# ---------------------------------------------------------------------------

STRINGS: Dict[str, Dict[str, str]] = {
    # ---- banner / startpage ----
    "banner.tagline": {
        "pl": "λambda Lab · Falenty 2026 · wtyczki, kable i krokodyle",
        "en": "λambda Lab · Falenty 2026 · plugs, cables and crocodiles",
    },
    "banner.version": {
        "pl": "wersja {version}",
        "en": "version {version}",
    },
    "banner.title": {
        "pl": " Wtyczki, kable i krokodyle — rzecz o rachunku λ ",
        "en": " Plugs, Cables and Crocodiles — On the Lambda Calculus ",
    },
    "banner.subtitle": {
        "pl": "dr Bartosz Naskręcki · UAM / CWSI PW",
        "en": "dr Bartosz Naskręcki · Adam Mickiewicz University · Center for Trustworthy AI WUT",
    },
    "banner.commands": {"pl": "Komendy", "en": "Commands"},
    "banner.col.cmd": {"pl": "Komenda", "en": "Command"},
    "banner.col.short": {"pl": "Skrót", "en": "Alias"},
    "banner.col.what": {"pl": "Co robi", "en": "What it does"},

    # ---- command descriptions in startpage table ----
    "cmd.tour": {
        "pl": "wycieczki dydaktyczne: ogólna + 9 wyspecjalizowanych (`tour list`, `tour <name>`, `tour all`)",
        "en": "guided tours: a general arc + 9 specialized ones (`tour list`, `tour <name>`, `tour all`)",
    },
    "cmd.lam": {
        "pl": "parsuje term, pokazuje drzewo AST i wolne zmienne",
        "en": "parse a term, show AST and free variables",
    },
    "cmd.reduce": {
        "pl": "β-redukcja krok po kroku z podświetleniem redeksu",
        "en": "step-by-step β-reduction with redex highlighting",
    },
    "cmd.church": {
        "pl": "rozwija stałe Churcha (TRUE, 3, PLUS, NAND, ...)",
        "en": "expand Church constants (TRUE, 3, PLUS, NAND, …)",
    },
    "cmd.peano": {
        "pl": "ewaluuje w arytmetyce Peano via Church encoding",
        "en": "evaluate in Peano arithmetic via Church encoding",
    },
    "cmd.alligators": {
        "pl": "rysuje term jako rodziny krokodyli (ASCII)",
        "en": "draw a term as alligator families (ASCII)",
    },
    "cmd.constants": {
        "pl": "tabela wszystkich stałych Churcha (NAND, SUB, Y, ...)",
        "en": "table of all Church constants (NAND, SUB, Y, …)",
    },
    "cmd.prove": {
        "pl": "automatyczny prover tautologii (De Morgan, ...)",
        "en": "automatic tautology prover (De Morgan, …)",
    },
    "cmd.lean": {
        "pl": "uruchamia / pokazuje dowód w Lean 4 (legacy 4.24)",
        "en": "run / show a Lean 4 proof (legacy 4.24)",
    },
    "cmd.arist": {
        "pl": "integracja z Aristotle (Harmonic AI) + GPT informalizacja",
        "en": "Aristotle (Harmonic AI) integration + GPT informalization",
    },
    "cmd.ag": {
        "pl": "odtwarza dowód AlphaGeometry DD+AR",
        "en": "replay AlphaGeometry DD+AR proof",
    },
    "cmd.quiz": {
        "pl": "losowe pytanie sprawdzające intuicję",
        "en": "random quiz question",
    },
    "cmd.help": {
        "pl": "pomoc — ogólna lub dla konkretnej komendy",
        "en": "help — general or for a specific command",
    },
    "cmd.clear": {"pl": "czyści ekran", "en": "clear the screen"},
    "cmd.quit": {"pl": "wyjście", "en": "quit"},
    "cmd.lang": {
        "pl": "przełącz język REPL (pl/en)",
        "en": "switch REPL language (pl/en)",
    },

    # ---- tips panel ----
    "tips.title": {"pl": "Wskazówki", "en": "Tips"},
    "tips.tab": {
        "pl": "TAB  podpowiada komendy i nazwy stałych.",
        "en": "TAB  completes commands and constant names.",
    },
    "tips.history": {
        "pl": "↑ ↓  przeglądają historię.",
        "en": "↑ ↓  browse the history.",
    },
    "tips.help": {
        "pl": "`help <komenda>` pokazuje szczegółowy opis.",
        "en": "`help <command>` shows a detailed description.",
    },
    "tips.exit": {
        "pl": "CTRL-D lub `quit` kończy sesję.",
        "en": "CTRL-D or `quit` ends the session.",
    },
    "tips.lang": {
        "pl": "`lang en` przełącza interfejs na angielski (`lang pl` z powrotem).",
        "en": "`lang pl` switches the interface back to Polish.",
    },

    # ---- repl prompts / messages ----
    "repl.farewell": {
        "pl": "Do zobaczenia, krokodylu 👋",
        "en": "See you in the swamp, crocodile 👋",
    },
    "repl.unknown": {
        "pl": "Nieznana komenda: {cmd}. Wpisz `help`.",
        "en": "Unknown command: {cmd}. Type `help`.",
    },
    "repl.exception": {
        "pl": "Wyjątek:",
        "en": "Exception:",
    },

    # ---- lang command ----
    "lang.usage": {
        "pl": "Użycie: lang <pl|en>. Bieżący: {current}.",
        "en": "Usage: lang <pl|en>. Current: {current}.",
    },
    "lang.unsupported": {
        "pl": "Nieobsługiwany język: {requested}. Wybierz `pl` lub `en`.",
        "en": "Unsupported language: {requested}. Choose `pl` or `en`.",
    },
    "lang.switched": {
        "pl": "Język REPL przełączony na: {lang}. Restart nie wymagany.",
        "en": "REPL language switched to: {lang}. No restart needed.",
    },
    "lang.persisted": {
        "pl": "Wybór zapisany w {path} — następny start REPL wczyta tę wartość.",
        "en": "Choice saved in {path} — next REPL start will use this value.",
    },

    # ---- help command ----
    "help.header": {
        "pl": "help: {name}",
        "en": "help: {name}",
    },
    "help.no_long": {
        "pl": "Nie mam rozszerzonej pomocy dla '{name}'.",
        "en": "No extended help available for '{name}'.",
    },
    "help.long.reduce": {
        "pl": (
            "[bold]reduce <term>[/bold]  ·  krok-po-kroku β-redukcja.\n\n"
            "Rozwija stałe Churcha (TRUE, PLUS, Y, NAND, SUB, ...) przed redukcją.\n"
            "Każdy krok pokazuje redeks na żółto, wynik na zielono.\n\n"
            "[brand]Przykłady:[/brand]\n"
            "  reduce (\\x. x) y                  # 1 krok → y\n"
            "  reduce (\\x. x x)(\\y. y)           # 2 kroki → \\y. y\n"
            "  reduce AND TRUE FALSE             # 4 kroki → FALSE\n"
            "  reduce PLUS 2 3                   # 6 kroków → 5\n"
            "  reduce NAND TRUE TRUE             # → FALSE\n"
            "  reduce SUB 7 3                    # → 4\n"
        ),
        "en": (
            "[bold]reduce <term>[/bold]  ·  step-by-step β-reduction.\n\n"
            "Expands Church constants (TRUE, PLUS, Y, NAND, SUB, ...) before reducing.\n"
            "Each step highlights the redex in yellow and the result in green.\n\n"
            "[brand]Examples:[/brand]\n"
            "  reduce (\\x. x) y                  # 1 step → y\n"
            "  reduce (\\x. x x)(\\y. y)           # 2 steps → \\y. y\n"
            "  reduce AND TRUE FALSE             # 4 steps → FALSE\n"
            "  reduce PLUS 2 3                   # 6 steps → 5\n"
            "  reduce NAND TRUE TRUE             # → FALSE\n"
            "  reduce SUB 7 3                    # → 4\n"
        ),
    },
    "help.long.church": {
        "pl": (
            "[bold]church <expr>[/bold]  ·  rozwija stałe Churcha i dekoduje wynik.\n\n"
            "Jak reduce, plus automatyczne dekodowanie normalnej formy:\n"
            "liczbę Churcha zamienia na zwykłą liczbę, boolean na True/False.\n\n"
            "[brand]Przykłady:[/brand]\n"
            "  church 3                          # pokazuje λ-term dla 3\n"
            "  church AND TRUE FALSE             # → Church-boolean: False\n"
            "  church PLUS 2 3                   # → Liczba Churcha: 5\n"
            "  church MULT 3 4                   # → 12\n"
            "  church POW 2 5                    # → 32\n"
            "  church PRED 7                     # → 6\n"
            "  church SUB 10 3                   # → 7\n"
            "  church ISZERO 0                   # → True\n"
            "  church LEQ 2 3                    # → True\n"
            "  church XOR TRUE TRUE              # → False\n"
        ),
        "en": (
            "[bold]church <expr>[/bold]  ·  expand Church constants and decode the result.\n\n"
            "Like reduce, plus automatic decoding of the normal form:\n"
            "a Church numeral becomes an ordinary number, a Church boolean becomes True/False.\n\n"
            "[brand]Examples:[/brand]\n"
            "  church 3                          # show the λ-term for 3\n"
            "  church AND TRUE FALSE             # → Church boolean: False\n"
            "  church PLUS 2 3                   # → Church numeral: 5\n"
            "  church MULT 3 4                   # → 12\n"
            "  church POW 2 5                    # → 32\n"
            "  church PRED 7                     # → 6\n"
            "  church SUB 10 3                   # → 7\n"
            "  church ISZERO 0                   # → True\n"
            "  church LEQ 2 3                    # → True\n"
            "  church XOR TRUE TRUE              # → False\n"
        ),
    },
    "help.long.peano": {
        "pl": (
            "[bold]peano <wyrażenie>[/bold]  ·  arytmetyka w stylu Peano.\n\n"
            "Akceptuje aliasy (case-insensitive): succ, pred, plus/add, sub/minus,\n"
            "mult/times, pow, iszero, leq, eq, and, or, not, if, 0/zero.\n\n"
            "[brand]Przykłady:[/brand]\n"
            "  peano succ (succ 0)               # → 2\n"
            "  peano plus 2 3                    # → 5\n"
            "  peano times 3 4                   # → 12\n"
            "  peano minus 7 3                   # → 4\n"
            "  peano pred 5                      # → 4\n"
            "  peano pow 2 4                     # → 16\n"
            "  peano iszero (pred 1)             # → True\n"
            "  peano leq 3 5                     # → True\n"
        ),
        "en": (
            "[bold]peano <expression>[/bold]  ·  Peano-style arithmetic.\n\n"
            "Accepts aliases (case-insensitive): succ, pred, plus/add, sub/minus,\n"
            "mult/times, pow, iszero, leq, eq, and, or, not, if, 0/zero.\n\n"
            "[brand]Examples:[/brand]\n"
            "  peano succ (succ 0)               # → 2\n"
            "  peano plus 2 3                    # → 5\n"
            "  peano times 3 4                   # → 12\n"
            "  peano minus 7 3                   # → 4\n"
            "  peano pred 5                      # → 4\n"
            "  peano pow 2 4                     # → 16\n"
            "  peano iszero (pred 1)             # → True\n"
            "  peano leq 3 5                     # → True\n"
        ),
    },
    "help.long.alligators": {
        "pl": (
            "[bold]alligators <term>[/bold]  ·  wizualizacja jako rodziny krokodyli.\n\n"
            "Głodny aligator = λ-abstrakcja. Stary = nawiasy. Jajko = zmienna.\n\n"
            "[brand]Przykłady:[/brand]\n"
            "  alligators (\\x. x x)(\\y. y)       # omega-like z natychmiastowym jedzeniem\n"
            "  alligators TRUE                   # pojedyncza abstrakcja z jajkiem\n"
            "  alligators AND                    # struktura AND-a\n"
            "  alligators (\\f x. f (f x))        # liczba Churcha 2\n"
        ),
        "en": (
            "[bold]alligators <term>[/bold]  ·  visualisation as alligator families (Bret Victor).\n\n"
            "Hungry alligator = λ-abstraction. Old alligator = parentheses. Egg = variable.\n\n"
            "[brand]Examples:[/brand]\n"
            "  alligators (\\x. x x)(\\y. y)       # omega-like, eaten right away\n"
            "  alligators TRUE                   # a single abstraction with an egg\n"
            "  alligators AND                    # structure of AND\n"
            "  alligators (\\f x. f (f x))        # Church numeral 2\n"
        ),
    },
    "help.long.constants": {
        "pl": (
            "[bold]constants [filtr][/bold]  ·  tabela wszystkich stałych Churcha.\n\n"
            "Grupuje stałe w sekcje: wartości logiczne, spójniki, pary, liczby,\n"
            "predykaty, rekursja, dywergencja.\n\n"
            "[brand]Przykłady:[/brand]\n"
            "  constants                         # wszystkie stałe\n"
            "  constants AND                     # tylko te, które zawierają 'AND'\n"
            "  constants PLUS                    # tylko PLUS\n"
        ),
        "en": (
            "[bold]constants [filter][/bold]  ·  table of all Church constants.\n\n"
            "Groups constants into sections: booleans, connectives, pairs, numerals,\n"
            "predicates, recursion, divergence.\n\n"
            "[brand]Examples:[/brand]\n"
            "  constants                         # all constants\n"
            "  constants AND                     # only those containing 'AND'\n"
            "  constants PLUS                    # only PLUS\n"
        ),
    },
    "help.long.prove": {
        "pl": (
            "[bold]prove [slug|formuła] [--trace] [--fusion][/bold]  ·  prover.\n\n"
            "Dwa tryby dowodzenia:\n"
            "  • domyślny — tabela prawdy z β-redukcją Church booleans;\n"
            "  • --fusion — symboliczna Shannon expansion + IF-FUSION\n"
            "    (bez enumeracji wartościowań, eleganckie drzewo decyzyjne).\n\n"
            "[brand]Przykłady:[/brand]\n"
            "  prove list                        # katalog twierdzeń\n"
            "  prove demorgan1                   # prawo De Morgana I\n"
            "  prove demorgan1 --fusion          # ten sam dowód przez IF-FUSION\n"
            "  prove excluded_middle             # A ∨ ¬A\n"
            "  prove modus_ponens --fusion       # (A ∧ (A⇒B)) ⇒ B symbolicznie\n"
            "  prove 'A AND B IMPLIES A'         # własna formuła\n"
            "  prove demorgan1 --trace           # z pełnym śladem β-redukcji\n"
        ),
        "en": (
            "[bold]prove [slug|formula] [--trace] [--fusion][/bold]  ·  prover.\n\n"
            "Two proving modes:\n"
            "  • default — truth table with β-reduction over Church booleans;\n"
            "  • --fusion — symbolic Shannon expansion + IF-FUSION\n"
            "    (no enumeration of valuations, an elegant decision tree).\n\n"
            "[brand]Examples:[/brand]\n"
            "  prove list                        # catalogue of theorems\n"
            "  prove demorgan1                   # De Morgan's first law\n"
            "  prove demorgan1 --fusion          # the same proof via IF-FUSION\n"
            "  prove excluded_middle             # A ∨ ¬A\n"
            "  prove modus_ponens --fusion       # (A ∧ (A⇒B)) ⇒ B symbolically\n"
            "  prove 'A AND B IMPLIES A'         # your own formula\n"
            "  prove demorgan1 --trace           # with the full β-reduction trace\n"
        ),
    },
    "help.long.lam": {
        "pl": (
            "[bold]lam <term>[/bold] (także λ, l)  ·  parsuje term i pokazuje AST.\n\n"
            "Rozwija stałe Churcha, podaje wolne zmienne i rysuje drzewo składniowe.\n\n"
            "[brand]Przykłady:[/brand]\n"
            "  lam \\x y. x (y z)                 # {z} wolna\n"
            "  lam AND TRUE FALSE                # pełne drzewo aplikacji\n"
            "  lam Y                             # struktura Y-kombinatora\n"
        ),
        "en": (
            "[bold]lam <term>[/bold] (also λ, l)  ·  parse a term and show the AST.\n\n"
            "Expands Church constants, lists free variables and draws the syntax tree.\n\n"
            "[brand]Examples:[/brand]\n"
            "  lam \\x y. x (y z)                 # {z} is free\n"
            "  lam AND TRUE FALSE                # the full application tree\n"
            "  lam Y                             # structure of the Y-combinator\n"
        ),
    },
    "help.long.lean": {
        "pl": (
            "[bold]lean <demo>[/bold]  ·  uruchamia / pokazuje dowód w Lean 4.\n\n"
            "Jeśli Lean jest zainstalowany — kompiluje i pokazuje wyjście.\n"
            "Jeśli nie — pokazuje wcześniej przygotowany ślad tactic state.\n\n"
            "[brand]Dostępne dema:[/brand]\n"
            "  and_comm        przemienność koniunkcji\n"
            "  imp_comp        składanie implikacji\n"
            "  congr           kongruencja równości\n"
            "  exists_square   ∃ n. n² = 4\n"
            "  term_proofs     klasyczne kombinatory (I, K, S, modus ponens)\n"
            "  nng             Natural Number Game — indukcja, add_comm, add_assoc\n"
            "  macbeth         Heather Macbeth „Mechanics of Proof” — bloki calc\n"
            "  erdos           Erdős #728 — pierwszy problem rozwiązany autonomicznie przez AI\n"
        ),
        "en": (
            "[bold]lean <demo>[/bold]  ·  run / show a Lean 4 proof.\n\n"
            "If Lean is installed — compile and show the output.\n"
            "If not — show a pre-recorded tactic-state trace.\n\n"
            "[brand]Available demos:[/brand]\n"
            "  and_comm        commutativity of conjunction\n"
            "  imp_comp        implication composition\n"
            "  congr           congruence of equality\n"
            "  exists_square   ∃ n. n² = 4\n"
            "  term_proofs     classic combinators (I, K, S, modus ponens)\n"
            "  nng             Natural Number Game — induction, add_comm, add_assoc\n"
            "  macbeth         Heather Macbeth \"Mechanics of Proof\" — calc blocks\n"
            "  erdos           Erdős #728 — the first problem solved autonomously by AI\n"
        ),
    },
    "help.long.ag": {
        "pl": (
            "[bold]ag [demo][/bold]  ·  odtwarzacz dowodów DD+AR AlphaGeometry.\n\n"
            "Bez argumentu wypisuje listę dostępnych. Z argumentem odtwarza kroki\n"
            "deduktywne + algebraiczne, naciśnij ENTER by przejść do kolejnego.\n\n"
            "[brand]Dostępne dema:[/brand]\n"
            "  angle_bisector  dwusieczna = wysokość w trójkącie równoramiennym\n"
            "  isogonal        izogonalne sprzężenie i okrąg\n"
            "  imo_p4          szkic zadania olimpijskiego z dodatkową konstrukcją\n"
        ),
        "en": (
            "[bold]ag [demo][/bold]  ·  AlphaGeometry DD+AR proof player.\n\n"
            "Without arguments — list available demos. With one — replay the\n"
            "deductive + algebraic steps; press ENTER for the next one.\n\n"
            "[brand]Available demos:[/brand]\n"
            "  angle_bisector  angle bisector = altitude in an isosceles triangle\n"
            "  isogonal        isogonal conjugation and a circle\n"
            "  imo_p4          olympiad problem sketch with an auxiliary construction\n"
        ),
    },
    "help.long.tour": {
        "pl": (
            "[bold]tour [name][/bold]  ·  wycieczki dydaktyczne po Lambda Lab.\n\n"
            "Bez argumentu — uruchamia [brand]general[/brand], dziesięciokrokowa wycieczka\n"
            "od wtyczek Amazonu przez krokodyle, β-redukcję, Church, rekursję,\n"
            "Curry-Howarda, Lean, aż po AlphaGeometry.\n\n"
            "[brand]Składnia:[/brand]\n"
            "  tour                 uruchamia tour ogólny (general)\n"
            "  tour list            tabela wszystkich wycieczek\n"
            "  tour <name>          wybrana wycieczka\n"
            "  tour all             wszystkie wycieczki po kolei\n"
            "  tour <name> --no-wait    bez ENTER (do screencastów)\n\n"
            "[brand]Dostępne wycieczki:[/brand]\n"
            "  general      pełen łuk: krokodyle → λ → Church → Lean → AG (~10 min)\n"
            "  lambda       wnętrze λ: parser, β/α/η, postać normalna, dywergencja\n"
            "  church       Church: TRUE/FALSE, NAND/XOR, liczby, PLUS/MULT, pary\n"
            "  peano        arytmetyka Peano przez Church (succ, plus, sub, leq)\n"
            "  prove        automatyczny prover: tablice prawdy + IF-FUSION\n"
            "  lean         dema Lean 4: and_comm, NNG, Macbeth, Erdős, term proofs\n"
            "  ag           AlphaGeometry: angle bisector, isogonal, IMO P4\n"
            "  arist        Aristotle: key → demo → watch → compile → informal → pdf\n"
            "  ch           Curry-Howard playground: term, type, lib, lean, build\n"
            "  alligators   gra Breta Victora: figury, β, α, reguła starości\n"
        ),
        "en": (
            "[bold]tour [name][/bold]  ·  guided tours of Lambda Lab.\n\n"
            "Without arguments — runs [brand]general[/brand], the ten-step tour from\n"
            "Amazon plugs through alligators, beta-reduction, Church, recursion,\n"
            "Curry-Howard, Lean, all the way to AlphaGeometry.\n\n"
            "[brand]Syntax:[/brand]\n"
            "  tour                 run the general tour\n"
            "  tour list            show the table of available tours\n"
            "  tour <name>          run a specialized tour\n"
            "  tour all             run every tour back-to-back\n"
            "  tour <name> --no-wait    skip ENTER prompts (for screen recordings)\n\n"
            "[brand]Available tours:[/brand]\n"
            "  general      the full arc: alligators -> lambda -> Church -> Lean -> AG (~10 min)\n"
            "  lambda       lambda internals: parser, beta/alpha/eta, normal form, divergence\n"
            "  church       Church: TRUE/FALSE, NAND/XOR, numerals, PLUS/MULT, pairs\n"
            "  peano        Peano arithmetic via Church (succ, plus, sub, leq)\n"
            "  prove        automatic prover: truth tables + IF-FUSION\n"
            "  lean         Lean 4 demos: and_comm, NNG, Macbeth, Erdos, term proofs\n"
            "  ag           AlphaGeometry: angle bisector, isogonal, IMO P4\n"
            "  arist        Aristotle: key -> demo -> watch -> compile -> informal -> pdf\n"
            "  ch           Curry-Howard playground: term, type, lib, lean, build\n"
            "  alligators   Bret Victor's game: pieces, beta, alpha, old-age rule\n"
        ),
    },
    "help.long.quiz": {
        "pl": (
            "[bold]quiz [pod-komenda] [opcje][/bold]  ·  pytania, sesje, pakiety, tabela wynikow.\n\n"
            "[brand]Pod-komendy:[/brand]\n"
            "  [accent]quiz[/accent]                            jedno losowe pytanie (legacy)\n"
            "  [accent]quiz --online[/accent]                   z fallbackiem na sedziego LLM\n"
            "  [accent]quiz --strict[/accent]                   tylko doslowne dopasowanie\n"
            "  [accent]quiz batch N[/accent]                    sesja N pytan z fullscreen UI\n"
            "  [accent]quiz bundles[/accent]                    lista wbudowanych pakietow\n"
            "  [accent]quiz topics[/accent]                     tabela tematow + liczba pytan\n"
            "  [accent]quiz types[/accent]                      tabela typow pytan + liczba\n"
            "  [accent]quiz score[/accent]                      historia ostatnich prob\n\n"
            "[brand]Filtry trybu batch:[/brand]\n"
            "  --topics church,peano       wybierz tematy (CSV)\n"
            "  --types open,mc,tf          wybierz typy pytan (CSV)\n"
            "  --difficulty 1-3            zakres trudnosci (1-5)\n"
            "  --bundle midterm_exam       uzyj pakietu zamiast filtrow\n"
            "  --no-clear                  nie czysc ekranu (do nagrywania)\n"
            "  --seed 42                   deterministyczna sesja\n"
            "  --online / --strict         tak samo jak w trybie pojedynczym\n\n"
            "[brand]Lokalny matcher (typ open) rozpoznaje:[/brand]\n"
            "  • [bold]exact[/bold]      — identyczny tekst\n"
            "  • [bold]whitespace[/bold] — identyczny po normalizacji bialych znakow\n"
            "  • [bold]alpha[/bold]      — α-rownowazne (np. `\\x. x` ≡ `\\y. y`)\n"
            "  • [bold]alpha+beta[/bold] — α-rownowazne po β-redukcji do postaci normalnej\n"
            "  • [bold]substring[/bold]  — Twoja odpowiedz jest podciagiem kanonicznej\n\n"
            "[brand]Typy pytan:[/brand]\n"
            "  • open       — krotka odpowiedz tekstowa (matcher j.w.)\n"
            "  • mc         — wybor A/B/C/D\n"
            "  • tf         — prawda / falsz (T/F, yes/no, 1/0)\n"
            "  • completion — uzupelnij brakujacy fragment\n"
            "  • code       — wpisz λ-term, walidator sprawdza zachowanie\n\n"
            "[brand]Sterowanie w trybie batch:[/brand]\n"
            "  ENTER po odpowiedzi · `s` pomin pytanie · `q` zakoncz wczesniej.\n\n"
            "[brand]Tryb --online:[/brand]\n"
            "  Wymaga klucza w [bold]~/.config/openai/env[/bold].\n"
            "  Aktywny tylko dla typu `open`. Bez klucza — fallback do lokalnego.\n\n"
            "[brand]Przyklady:[/brand]\n"
            "  quiz                                  # legacy single\n"
            "  quiz batch 10 --topics church         # 10 pytan z Churcha\n"
            "  quiz batch --bundle intro_lambda      # wbudowany pakiet\n"
            "  quiz batch 20 --types mc,tf --difficulty 1-2\n"
            "  quiz score --last 10                  # ostatnie 10 prob\n"
            "  quiz score --reset                    # wyczysc tabele wynikow\n"
        ),
        "en": (
            "[bold]quiz [sub-command] [opts][/bold]  ·  questions, sessions, bundles, scoreboard.\n\n"
            "[brand]Sub-commands:[/brand]\n"
            "  [accent]quiz[/accent]                            one random question (legacy)\n"
            "  [accent]quiz --online[/accent]                   with LLM judge fallback\n"
            "  [accent]quiz --strict[/accent]                   exact match only\n"
            "  [accent]quiz batch N[/accent]                    a session of N questions with fullscreen UI\n"
            "  [accent]quiz bundles[/accent]                    list built-in bundles\n"
            "  [accent]quiz topics[/accent]                     topic table + question counts\n"
            "  [accent]quiz types[/accent]                      question-type table + counts\n"
            "  [accent]quiz score[/accent]                      recent attempts\n\n"
            "[brand]Batch filters:[/brand]\n"
            "  --topics church,peano       pick topics (CSV)\n"
            "  --types open,mc,tf          pick types (CSV)\n"
            "  --difficulty 1-3            difficulty range (1-5)\n"
            "  --bundle midterm_exam       use a bundle instead of filters\n"
            "  --no-clear                  do not clear the screen (for recording)\n"
            "  --seed 42                   deterministic session\n"
            "  --online / --strict         same as in single mode\n\n"
            "[brand]Local matcher (open type) recognizes:[/brand]\n"
            "  • [bold]exact[/bold]      — identical text\n"
            "  • [bold]whitespace[/bold] — identical after whitespace normalization\n"
            "  • [bold]alpha[/bold]      — α-equivalent (e.g. `\\x. x` ≡ `\\y. y`)\n"
            "  • [bold]alpha+beta[/bold] — α-equivalent after β-reducing to normal form\n"
            "  • [bold]substring[/bold]  — your answer is a substring of the canonical\n\n"
            "[brand]Question types:[/brand]\n"
            "  • open       — short text answer (matcher above)\n"
            "  • mc         — choose A/B/C/D\n"
            "  • tf         — true / false (T/F, yes/no, 1/0)\n"
            "  • completion — fill in the missing fragment\n"
            "  • code       — write a λ-term, the validator runs it\n\n"
            "[brand]Batch controls:[/brand]\n"
            "  ENTER after answer · `s` skip · `q` quit early.\n\n"
            "[brand]--online mode:[/brand]\n"
            "  Needs a key in [bold]~/.config/openai/env[/bold].\n"
            "  Only used for `open` questions. No key — falls back to local.\n\n"
            "[brand]Examples:[/brand]\n"
            "  quiz                                  # legacy single\n"
            "  quiz batch 10 --topics church         # 10 Church questions\n"
            "  quiz batch --bundle intro_lambda      # a built-in bundle\n"
            "  quiz batch 20 --types mc,tf --difficulty 1-2\n"
            "  quiz score --last 10                  # last 10 attempts\n"
            "  quiz score --reset                    # reset the scoreboard\n"
        ),
    },
    # ---- tour command ----
    "tour.alligator_title": {
        "pl": "🐊 Alligator view",
        "en": "🐊 Alligator view",
    },
    "tour.next_prompt": {
        "pl": "ENTER → następny krok…",
        "en": "ENTER → next step…",
    },
    "tour.interrupted": {
        "pl": "Przerwano wycieczkę.",
        "en": "Tour interrupted.",
    },
    "tour.end": {
        "pl": "Koniec wycieczki",
        "en": "End of the tour",
    },
    "tour.step.1.title": {
        "pl": "1. Wtyczki, kable i paczki",
        "en": "1. Plugs, cables and parcels",
    },
    "tour.step.1.body": {
        "pl": (
            "Amazon używa języka Dafny, opartego na matematycznym rachunku,\n"
            "żeby formalnie weryfikować, że algorytm sortowania paczek jest poprawny.\n"
            "Ta matematyka pochodzi z lat 40. XX wieku — to **rachunek λ**."
        ),
        "en": (
            "Amazon uses Dafny, a language built on a mathematical calculus,\n"
            "to formally verify that its parcel-sorting algorithm is correct.\n"
            "That mathematics goes back to the 1940s — it is the **lambda calculus**."
        ),
    },
    "tour.step.2.title": {
        "pl": "2. Alligator Eggs",
        "en": "2. Alligator Eggs",
    },
    "tour.step.2.body": {
        "pl": (
            "Bret Victor stworzył grę, w której aligatory zjadają rodziny, a jajka się wylęgają.\n"
            "Ta gra to rachunek λ w przebraniu. Zobaczmy krokodyla:"
        ),
        "en": (
            "Bret Victor invented a game where alligators eat families and eggs hatch.\n"
            "That game is the lambda calculus in disguise. Let's meet an alligator:"
        ),
    },
    "tour.step.3.title": {
        "pl": "3. Identyczność — najprostszy term",
        "en": "3. Identity — the simplest term",
    },
    "tour.step.3.body": {
        "pl": "Term (λx. x) to identyczność: bierze argument i zwraca go bez zmian.",
        "en": "The term (λx. x) is the identity: it takes an argument and returns it unchanged.",
    },
    "tour.step.3.demo": {
        # Wartość zmiennej przekazywanej do identyczności — wybrana tak,
        # żeby narracja brzmiała naturalnie w danym języku.
        "pl": r"(\x. x) krokodyl",
        "en": r"(\x. x) crocodile",
    },
    "tour.step.4.title": {
        "pl": "4. β-redukcja na żywo",
        "en": "4. β-reduction in action",
    },
    "tour.step.4.body": {
        "pl": "Zastosowanie (λx. t) u jest zawsze takie samo: podstaw u za x w t.",
        "en": "Applying (λx. t) u is always the same: substitute u for x in t.",
    },
    "tour.step.5.title": {
        "pl": "5. TRUE, FALSE i IF",
        "en": "5. TRUE, FALSE and IF",
    },
    "tour.step.5.body": {
        "pl": (
            "W rachunku λ można kodować wartości logiczne. TRUE wybiera pierwszy argument,\n"
            "FALSE wybiera drugi. IF to zwykła aplikacja: IF b t f = b t f."
        ),
        "en": (
            "Booleans can be encoded in the lambda calculus. TRUE picks the first argument,\n"
            "FALSE picks the second. IF is just application: IF b t f = b t f."
        ),
    },
    "tour.step.6.title": {
        "pl": "6. Liczby Churcha",
        "en": "6. Church numerals",
    },
    "tour.step.6.body": {
        "pl": (
            "Liczba n to „n-krotne zastosowanie funkcji”.\n"
            "3 = λf x. f (f (f x)). SUCC dokłada kolejne f. PLUS składa iteracje."
        ),
        "en": (
            "The number n is \"apply a function n times\".\n"
            "3 = λf x. f (f (f x)). SUCC adds one more f. PLUS composes iterations."
        ),
    },
    "tour.step.7.title": {
        "pl": "7. Rekursja: kombinator Y",
        "en": "7. Recursion: the Y-combinator",
    },
    "tour.step.7.body": {
        "pl": (
            "Rachunek λ nie ma wbudowanej rekursji, ale można ją SKONSTRUOWAĆ.\n"
            "Y = λf. (λx. f (x x))(λx. f (x x)). To przepis na „samopowtarzanie”."
        ),
        "en": (
            "The lambda calculus has no built-in recursion — but you can CONSTRUCT it.\n"
            "Y = λf. (λx. f (x x))(λx. f (x x)). A recipe for \"self-replication\"."
        ),
    },
    "tour.step.8.title": {
        "pl": "8. Curry–Howard: dowód = program",
        "en": "8. Curry–Howard: proof = program",
    },
    "tour.step.8.body": {
        "pl": (
            "λx. x ma typ P → P. To jednocześnie funkcja identycznościowa\n"
            "ORAZ dowód twierdzenia „P implikuje P”."
        ),
        "en": (
            "λx. x has type P → P. It is at once the identity function\n"
            "AND a proof of the theorem \"P implies P\"."
        ),
    },
    "tour.step.9.title": {
        "pl": "9. Lean: współczesny rachunek λ",
        "en": "9. Lean: modern lambda calculus",
    },
    "tour.step.9.body": {
        "pl": (
            "Lean 4 to dojrzały asystent dowodzenia. Każdy dowód jest zapisanym termem.\n"
            "Uruchom `lean and_comm` żeby zobaczyć dowód przemienności koniunkcji."
        ),
        "en": (
            "Lean 4 is a mature proof assistant. Every proof is a written term.\n"
            "Run `lean and_comm` to see a proof of commutativity of conjunction."
        ),
    },
    "tour.step.10.title": {
        "pl": "10. AlphaGeometry: AI + symbol",
        "en": "10. AlphaGeometry: AI + symbol",
    },
    "tour.step.10.body": {
        "pl": (
            "AlphaGeometry od DeepMind łączy generatywny model języka z symbolicznym\n"
            "solverem DD+AR. Uruchom `ag angle_bisector`, aby zobaczyć ślad dowodu."
        ),
        "en": (
            "DeepMind's AlphaGeometry combines a generative language model with a symbolic\n"
            "DD+AR solver. Run `ag angle_bisector` to see a proof trace."
        ),
    },

    # ---- quiz command ----
    "quiz.title": {
        "pl": "🧩 Pytanko",
        "en": "🧩 Question",
    },
    "quiz.input": {
        "pl": "Twoja odpowiedź > ",
        "en": "Your answer > ",
    },
    "quiz.correct": {
        "pl": "✓ Tak!",
        "en": "✓ Correct!",
    },
    "quiz.my_answer": {
        "pl": "Moja odpowiedź: [brand]{answer}[/brand]",
        "en": "My answer: [brand]{answer}[/brand]",
    },
    "quiz.alpha_note": {
        "pl": "(α-równoważne — Twoja postać: [brand]{user}[/brand], kanoniczna: [brand]{canonical}[/brand])",
        "en": "(α-equivalent — your form: [brand]{user}[/brand], canonical: [brand]{canonical}[/brand])",
    },
    # Method labels — wyświetlane w nawiasie obok ✓ correct.
    "quiz.method.exact":      {"pl": "dokładne dopasowanie",            "en": "exact match"},
    "quiz.method.whitespace": {"pl": "dopasowane po spacjach",          "en": "matched after whitespace"},
    "quiz.method.alpha":      {"pl": "α-równoważne",                    "en": "α-equivalent"},
    "quiz.method.alpha+beta": {"pl": "α-równoważne po β-redukcji",      "en": "α-equivalent after β-reduction"},
    "quiz.method.substring":  {"pl": "podciąg",                         "en": "substring"},
    # Online mode messages.
    "quiz.suggest_online": {
        "pl": "Wskazówka: spróbuj `quiz --online`, by sędzia LLM ocenił Twoją odpowiedź.",
        "en": "Hint: try `quiz --online` to have an LLM judge your answer.",
    },
    "quiz.online.no_key": {
        "pl": "Tryb --online wymaga klucza OpenAI w ~/.config/openai/env. Brak klucza — używam trybu lokalnego.",
        "en": "--online mode needs an OpenAI key in ~/.config/openai/env. No key — falling back to local.",
    },
    "quiz.online.judging": {
        "pl": "🧠 Pytam sędziego LLM…",
        "en": "🧠 Asking the LLM judge…",
    },
    "quiz.online.failed": {
        "pl": "Sędzia LLM nie odpowiedział (sieć / model / parsing). Spadam do trybu lokalnego.",
        "en": "LLM judge did not respond (network / model / parsing). Falling back to local.",
    },
    "quiz.llm.accepted": {
        "pl": "✓ LLM uznał odpowiedź ({equivalence}) — {model} · {elapsed}s",
        "en": "✓ LLM accepted ({equivalence}) — {model} · {elapsed}s",
    },
    "quiz.llm.rejected": {
        "pl": "✗ LLM odrzucił odpowiedź ({equivalence}) — {model} · {elapsed}s",
        "en": "✗ LLM rejected ({equivalence}) — {model} · {elapsed}s",
    },
    "quiz.q.1": {
        "pl": r"Do czego zredukuje się (\x. x) krokodyl ?",
        "en": r"What does (\x. x) crocodile reduce to?",
    },
    "quiz.a.1": {
        "pl": "krokodyl",
        "en": "crocodile",
    },
    "quiz.h.1": {
        "pl": "Podstawiamy `krokodyl` za `x` w ciele `x`.",
        "en": "Substitute `crocodile` for `x` in the body `x`.",
    },
    "quiz.q.2": {
        "pl": r"Do czego zredukuje się (\x. x x)(\y. y) ?",
        "en": r"What does (\x. x x)(\y. y) reduce to?",
    },
    "quiz.a.2": {
        "pl": r"\y. y",
        "en": r"\y. y",
    },
    "quiz.h.2": {
        "pl": r"(\x. x x) podstawia y := (\y. y), daje (\y.y)(\y.y), co redukuje do \y.y.",
        "en": r"(\x. x x) substitutes y := (\y. y), giving (\y.y)(\y.y), which reduces to \y.y.",
    },
    "quiz.q.3": {
        "pl": "Co to jest Ω = (λx. x x)(λx. x x)?",
        "en": "What is Ω = (λx. x x)(λx. x x)?",
    },
    "quiz.a.3": {
        "pl": "term, który nie ma postaci normalnej",
        "en": "a term with no normal form",
    },
    "quiz.h.3": {
        "pl": "Każda β-redukcja daje z powrotem Ω.",
        "en": "Every β-reduction yields Ω again.",
    },
    "quiz.q.4": {
        "pl": "Jak zakodować liczbę 2 w Churchu?",
        "en": "How do you encode the number 2 as a Church numeral?",
    },
    "quiz.a.4": {
        "pl": r"\f x. f (f x)",
        "en": r"\f x. f (f x)",
    },
    "quiz.h.4": {
        "pl": "Liczba n = n-krotna aplikacja funkcji.",
        "en": "The number n = n-fold application of a function.",
    },
    "quiz.q.5": {
        "pl": "Ile wynosi IF TRUE a b?",
        "en": "What is IF TRUE a b?",
    },
    "quiz.a.5": {
        "pl": "a",
        "en": "a",
    },
    "quiz.h.5": {
        "pl": "TRUE = λt f. t wybiera pierwszy argument.",
        "en": "TRUE = λt f. t picks the first argument.",
    },
    "quiz.q.6": {
        "pl": "Jaki typ ma λx. x w STLC?",
        "en": "What is the type of λx. x in STLC?",
    },
    "quiz.a.6": {
        "pl": "P → P",
        "en": "P → P",
    },
    "quiz.h.6": {
        "pl": "Term-identyczność jest dowodem `P → P` via Curry–Howard.",
        "en": "The identity term is a proof of `P → P` via Curry–Howard.",
    },

    # ---- quiz: matcher method labels ----
    "quiz.method.exact": {"pl": "dosłownie", "en": "exact"},
    "quiz.method.whitespace": {"pl": "po normalizacji spacji", "en": "whitespace-normalised"},
    "quiz.method.alpha": {"pl": "α-równoważne", "en": "α-equivalent"},
    "quiz.method.alpha+beta": {"pl": "α-równoważne po β", "en": "α-equivalent after β"},
    "quiz.method.substring": {"pl": "podciąg", "en": "substring"},
    "quiz.method.empty": {"pl": "puste", "en": "empty"},
    "quiz.method.none": {"pl": "brak", "en": "no match"},

    # ---- quiz: online judge ----
    "quiz.suggest_online": {
        "pl": "Wskazówka: spróbuj `quiz --online` żeby zapytać sędziego LLM.",
        "en": "Hint: try `quiz --online` to consult the LLM judge.",
    },
    "quiz.online.no_key": {
        "pl": "Brak klucza OpenAI w ~/.config/openai/env — sędzia LLM niedostępny.",
        "en": "No OpenAI key in ~/.config/openai/env — LLM judge unavailable.",
    },
    "quiz.online.judging": {"pl": "Pytam sędziego LLM…", "en": "Asking the LLM judge..."},
    "quiz.online.failed": {
        "pl": "Sędzia LLM nie odpowiedział — fallback do lokalnego.",
        "en": "LLM judge did not respond — falling back to local.",
    },
    "quiz.llm.accepted": {
        "pl": "✓ LLM ({equivalence}, {model}, {elapsed}s)",
        "en": "✓ LLM ({equivalence}, {model}, {elapsed}s)",
    },
    "quiz.llm.rejected": {
        "pl": "✗ LLM ({equivalence}, {model}, {elapsed}s)",
        "en": "✗ LLM ({equivalence}, {model}, {elapsed}s)",
    },

    # ---- quiz: argument errors ----
    "quiz.argparse_err": {
        "pl": "Błąd parsowania argumentów: {error}",
        "en": "Argument parse error: {error}",
    },

    # ---- quiz: question-type labels ----
    "quiz.type.open": {"pl": "otwarte", "en": "open"},
    "quiz.type.mc": {"pl": "wielokrotny wybór", "en": "multiple choice"},
    "quiz.type.tf": {"pl": "prawda/fałsz", "en": "true/false"},
    "quiz.type.completion": {"pl": "uzupełnienie", "en": "completion"},
    "quiz.type.code": {"pl": "kod λ", "en": "λ-code"},

    # ---- quiz batch UI ----
    "quiz.batch.header": {
        "pl": "Pytanie {idx}/{total} · Temat: {topic} · Typ: {type} · Trudność: {difficulty}",
        "en": "Question {idx}/{total} · Topic: {topic} · Type: {type} · Difficulty: {difficulty}",
    },
    "quiz.batch.input": {"pl": "Twoja odpowiedź > ", "en": "Your answer > "},
    "quiz.batch.tf_hint": {
        "pl": "Wpisz T/F (lub yes/no, 1/0).",
        "en": "Enter T/F (or yes/no, 1/0).",
    },
    "quiz.batch.completion_hint": {
        "pl": "Uzupełnij brakujące słowo / wyrażenie.",
        "en": "Fill in the missing word / expression.",
    },
    "quiz.batch.code_hint": {
        "pl": "Wpisz pełny λ-term (stałe Churcha rozpoznawane).",
        "en": "Write a full λ-term (Church constants are recognised).",
    },
    "quiz.batch.feedback.correct": {"pl": "✓ Poprawnie!", "en": "✓ Correct!"},
    "quiz.batch.feedback.incorrect": {"pl": "✗ Niepoprawnie", "en": "✗ Incorrect"},
    "quiz.batch.canonical": {
        "pl": "Wzorcowa odpowiedź: [brand]{answer}[/brand]",
        "en": "Canonical answer: [brand]{answer}[/brand]",
    },
    "quiz.batch.no_explanation": {
        "pl": "(brak wyjaśnienia)",
        "en": "(no explanation)",
    },
    "quiz.batch.skipped": {"pl": "↷ Pominięte.", "en": "↷ Skipped."},
    "quiz.batch.no_questions": {
        "pl": "Brak pytań pasujących do filtru.",
        "en": "No questions match the filter.",
    },
    "quiz.batch.splash.title": {"pl": "Sesja Quiz", "en": "Quiz session"},
    "quiz.batch.splash.questions": {"pl": "Liczba pytań: {n}", "en": "Questions: {n}"},
    "quiz.batch.splash.topics": {"pl": "Tematy: {topics}", "en": "Topics: {topics}"},
    "quiz.batch.splash.types": {"pl": "Typy: {types}", "en": "Types: {types}"},
    "quiz.batch.splash.bundle": {"pl": "Pakiet: [accent]{bundle}[/accent]", "en": "Bundle: [accent]{bundle}[/accent]"},
    "quiz.batch.splash.any": {"pl": "(dowolne)", "en": "(any)"},
    "quiz.batch.splash.controls": {
        "pl": "Sterowanie: ENTER po odpowiedzi · `s` pomiń · `q` zakończ.",
        "en": "Controls: ENTER after answering · `s` skip · `q` quit.",
    },
    "quiz.batch.final.title": {"pl": "Wynik końcowy", "en": "Final score"},
    "quiz.batch.final.summary": {
        "pl": "Trafione: [brand]{correct}/{total}[/brand] ({pct}%)",
        "en": "Correct: [brand]{correct}/{total}[/brand] ({pct}%)",
    },
    "quiz.batch.final.skipped": {"pl": "Pominięte: {skipped}", "en": "Skipped: {skipped}"},
    "quiz.batch.final.duration": {"pl": "Czas: {seconds} s", "en": "Duration: {seconds} s"},
    "quiz.batch.final.by_topic": {"pl": "Wg tematu:", "en": "By topic:"},
    "quiz.batch.final.by_type": {"pl": "Wg typu:", "en": "By type:"},

    # ---- quiz batch: per-question review of mistakes ----
    "quiz.batch.review.title": {
        "pl": "Przegląd błędów",
        "en": "Mistakes review",
    },
    "quiz.batch.review.perfect": {
        "pl": "🎉 Bezbłędna sesja! Nic do poprawy.",
        "en": "🎉 Flawless session — nothing to review.",
    },
    "quiz.batch.review.col.topic":    {"pl": "Temat",       "en": "Topic"},
    "quiz.batch.review.col.type":     {"pl": "Typ",         "en": "Type"},
    "quiz.batch.review.col.question": {"pl": "Pytanie",     "en": "Question"},
    "quiz.batch.review.col.your":     {"pl": "Twoja odp.",  "en": "Your answer"},
    "quiz.batch.review.col.correct":  {"pl": "Poprawna",    "en": "Correct"},
    "quiz.batch.review.skipped_label": {"pl": "(pominięte)", "en": "(skipped)"},
    "quiz.batch.review.code_expected": {
        "pl": "λ-term redukujący się do {expected}",
        "en": "λ-term reducing to {expected}",
    },
    "quiz.batch.review.explanations": {
        "pl": "Wyjaśnienia:",
        "en": "Explanations:",
    },

    # ---- quiz topics / types / bundles tables ----
    "quiz.topics.title": {"pl": "Tematy quizu", "en": "Quiz topics"},
    "quiz.topics.col.topic": {"pl": "Temat", "en": "Topic"},
    "quiz.topics.col.count": {"pl": "Liczba", "en": "Count"},
    "quiz.topics.empty": {"pl": "Brak tematów.", "en": "No topics."},
    "quiz.types.title": {"pl": "Typy pytań", "en": "Question types"},
    "quiz.types.col.type": {"pl": "Typ", "en": "Type"},
    "quiz.types.col.label": {"pl": "Opis", "en": "Label"},
    "quiz.types.col.count": {"pl": "Liczba", "en": "Count"},
    "quiz.types.empty": {"pl": "Brak typów.", "en": "No types."},
    "quiz.bundles.title": {"pl": "Pakiety pytań", "en": "Question bundles"},
    "quiz.bundles.col.id": {"pl": "ID", "en": "ID"},
    "quiz.bundles.col.title": {"pl": "Tytuł", "en": "Title"},
    "quiz.bundles.col.n": {"pl": "Pytań", "en": "Q"},
    "quiz.bundles.col.duration": {"pl": "Czas", "en": "Time"},
    "quiz.bundles.col.description": {"pl": "Opis", "en": "Description"},
    "quiz.bundles.empty": {"pl": "Brak pakietów.", "en": "No bundles defined."},

    # ---- quiz score table ----
    "quiz.score.title": {"pl": "Historia wyników", "en": "Score history"},
    "quiz.score.col.ts": {"pl": "Kiedy", "en": "When"},
    "quiz.score.col.bundle": {"pl": "Pakiet", "en": "Bundle"},
    "quiz.score.col.score": {"pl": "Wynik", "en": "Score"},
    "quiz.score.col.pct": {"pl": "%", "en": "%"},
    "quiz.score.col.duration": {"pl": "Czas", "en": "Duration"},
    "quiz.score.col.lang": {"pl": "Lang", "en": "Lang"},
    "quiz.score.empty": {"pl": "Brak zapisanych prób.", "en": "No recorded attempts."},
    "quiz.score.reset_ok": {"pl": "Tabela wyników wyczyszczona.", "en": "Scoreboard cleared."},
    "quiz.score.reset_fail": {
        "pl": "Nie udało się wyczyścić tabeli wyników.",
        "en": "Could not reset the scoreboard.",
    },

    # ---- common ----
    "common.parse_error": {
        "pl": "Błąd składni:",
        "en": "Parse error:",
    },

    # ---- reduce command ----
    "reduce.usage": {
        "pl": "Użycie: reduce <term>",
        "en": "Usage: reduce <term>",
    },
    "reduce.decoded.numeral": {
        "pl": "🐊 Wynik wygląda jak liczba Churcha:",
        "en": "🐊 The result looks like a Church numeral:",
    },
    "reduce.decoded.bool": {
        "pl": "🐊 Wynik wygląda jak Church-boolean:",
        "en": "🐊 The result looks like a Church boolean:",
    },

    # ---- church command ----
    "church.table.title": {
        "pl": "Kodowania Churcha",
        "en": "Church encodings",
    },
    "church.col.name": {
        "pl": "Nazwa",
        "en": "Name",
    },
    "church.col.term": {
        "pl": "λ-term",
        "en": "λ-term",
    },
    "church.expanded_panel": {
        "pl": "Po rozwinięciu stałych",
        "en": "After expanding constants",
    },
    "church.dec.numeral": {
        "pl": "🐊 Liczba Churcha: [brand]{value}[/brand]",
        "en": "🐊 Church numeral: [brand]{value}[/brand]",
    },
    "church.dec.bool": {
        "pl": "🐊 Church-boolean: [brand]{value}[/brand]",
        "en": "🐊 Church boolean: [brand]{value}[/brand]",
    },
    "church.dec.ambiguous": {
        "pl": (
            "[muted]λt f. f jest jednocześnie liczbą Churcha 0 oraz wartością"
            " FALSE — to nie jest błąd, tylko nieoznaczoność kodowania Churcha.[/muted]"
        ),
        "en": (
            "[muted]λt f. f is at once the Church numeral 0 and the value FALSE"
            " — not a bug, just an inherent ambiguity of Church encoding.[/muted]"
        ),
    },
    "church.dec.title": {
        "pl": "Dekodowanie",
        "en": "Decoding",
    },

    # ---- peano command ----
    "peano.usage": {
        "pl": "Użycie: peano <wyrażenie> (np. `peano plus 2 3`)",
        "en": "Usage: peano <expression> (e.g. `peano plus 2 3`)",
    },
    "peano.rewrite": {
        "pl": "→ przepisuję jako:",
        "en": "→ rewriting as:",
    },

    # ---- alligators command ----
    "alligators.usage": {
        "pl": "Użycie: alligators <term>",
        "en": "Usage: alligators <term>",
    },
    "alligators.title": {
        "pl": "🐊 Alligator Eggs view",
        "en": "🐊 Alligator Eggs view",
    },
    "alligators.legend": {
        "pl": (
            "🐊 Krokodyl mówi: każdy zielony kwadrat to głodny aligator (λ). "
            "Jajko (🥚) to zmienna. Szara ramka to „rodzina” otoczona parą nawiasów."
        ),
        "en": (
            "🐊 The crocodile says: every green square is a hungry alligator (λ). "
            "An egg (🥚) is a variable. The grey frame is a \"family\" wrapped in a pair of parentheses."
        ),
    },

    # ---- lam command ----
    "lam.usage": {
        "pl": "Użycie: λ <term>",
        "en": "Usage: λ <term>",
    },
    "lam.row.pretty": {
        "pl": "pretty",
        "en": "pretty",
    },
    "lam.row.free": {
        "pl": "wolne zmienne",
        "en": "free variables",
    },
    "lam.row.free.none": {
        "pl": "(brak)",
        "en": "(none)",
    },
    "lam.panel.term": {
        "pl": "Term",
        "en": "Term",
    },
    "lam.panel.tree": {
        "pl": "Drzewo AST",
        "en": "AST tree",
    },

    # ---- constants command ----
    "constants.group.bools": {
        "pl": "Wartości logiczne",
        "en": "Booleans",
    },
    "constants.group.connectives": {
        "pl": "Spójniki",
        "en": "Connectives",
    },
    "constants.group.pairs": {
        "pl": "Pary",
        "en": "Pairs",
    },
    "constants.group.numerals": {
        "pl": "Liczby i arytmetyka",
        "en": "Numerals and arithmetic",
    },
    "constants.group.predicates": {
        "pl": "Predykaty / porównania",
        "en": "Predicates / comparisons",
    },
    "constants.group.recursion": {
        "pl": "Rekursja",
        "en": "Recursion",
    },
    "constants.group.divergence": {
        "pl": "Dywergencja",
        "en": "Divergence",
    },
    "constants.col.name": {
        "pl": "Nazwa",
        "en": "Name",
    },
    "constants.col.term": {
        "pl": "λ-term",
        "en": "λ-term",
    },
    "constants.usage_hint": {
        "pl": (
            "[muted]Użycie w innych komendach:[/muted]  "
            "[brand]reduce NAND TRUE FALSE[/brand]  ·  "
            "[brand]church PLUS 2 3[/brand]  ·  "
            "[brand]peano minus 5 3[/brand]"
        ),
        "en": (
            "[muted]Use in other commands:[/muted]  "
            "[brand]reduce NAND TRUE FALSE[/brand]  ·  "
            "[brand]church PLUS 2 3[/brand]  ·  "
            "[brand]peano minus 5 3[/brand]"
        ),
    },

    # ---- prove command ----
    "prove.lambda_encoding": {
        "pl": "Kodowanie w rachunku λ",
        "en": "Lambda-calculus encoding",
    },
    "prove.row.lhs": {"pl": "lhs", "en": "lhs"},
    "prove.row.rhs": {"pl": "rhs", "en": "rhs"},
    "prove.tt.title": {"pl": "Tabela prawdy", "en": "Truth table"},
    "prove.tt.col.result": {"pl": "wynik", "en": "result"},
    "prove.tt.col.steps": {"pl": "β-kroków", "en": "β-steps"},
    "prove.tt.col.l": {"pl": "L", "en": "L"},
    "prove.tt.col.r": {"pl": "R", "en": "R"},
    "prove.tt.col.match": {"pl": "L = R ?", "en": "L = R ?"},
    "prove.tt.col.beta": {"pl": "β", "en": "β"},
    "prove.concl.taut": {
        "pl": "✓ Formuła [brand]{title}[/brand] jest [ok]tautologią[/ok].",
        "en": "✓ The formula [brand]{title}[/brand] is a [ok]tautology[/ok].",
    },
    "prove.concl.equiv": {
        "pl": "✓ Równoważność [brand]{title}[/brand] zachodzi przy każdym wartościowaniu. [ok]QED[/ok].",
        "en": "✓ The equivalence [brand]{title}[/brand] holds for every assignment. [ok]QED[/ok].",
    },
    "prove.concl.title.ok": {
        "pl": "Dowód sprawdzony",
        "en": "Proof verified",
    },
    "prove.concl.fail": {
        "pl": "✗ Formuła [brand]{title}[/brand] NIE jest tautologią — istnieje wartościowanie, które daje FALSE.",
        "en": "✗ The formula [brand]{title}[/brand] is NOT a tautology — there is an assignment that yields FALSE.",
    },
    "prove.concl.title.fail": {
        "pl": "Nie jest tautologią",
        "en": "Not a tautology",
    },
    "prove.trace_title": {
        "pl": "Ślad β-redukcji dla wartościowania {assignment}",
        "en": "β-reduction trace for assignment {assignment}",
    },
    "prove.catalog.title": {
        "pl": "Katalog twierdzeń (prove <slug>)",
        "en": "Theorem catalogue (prove <slug>)",
    },
    "prove.catalog.col.slug": {"pl": "slug", "en": "slug"},
    "prove.catalog.col.title": {"pl": "tytuł", "en": "title"},
    "prove.catalog.col.formula": {"pl": "formuła", "en": "formula"},
    "prove.catalog.usage": {
        "pl": (
            "\n[narrator]Użycie:[/narrator]  "
            "[brand]prove demorgan1[/brand]  ·  "
            "[brand]prove 'A AND B IMPLIES A'[/brand]  ·  "
            "[brand]prove list[/brand]"
        ),
        "en": (
            "\n[narrator]Usage:[/narrator]  "
            "[brand]prove demorgan1[/brand]  ·  "
            "[brand]prove 'A AND B IMPLIES A'[/brand]  ·  "
            "[brand]prove list[/brand]"
        ),
    },
    "prove.custom.iff_title": {
        "pl": "Wprowadzone twierdzenie (równoważność)",
        "en": "User-supplied theorem (equivalence)",
    },
    "prove.custom.iff_comment": {
        "pl": "Formuła wprowadzona przez użytkownika.",
        "en": "Formula supplied by the user.",
    },
    "prove.custom.taut_title": {
        "pl": "Wprowadzone twierdzenie",
        "en": "User-supplied theorem",
    },
    "prove.custom.taut_comment": {
        "pl": "Formuła wprowadzona przez użytkownika. Sprawdzamy, czy jest tautologią.",
        "en": "Formula supplied by the user. We check whether it is a tautology.",
    },
    "prove.fusion.rule_header": {
        "pl": "IF-FUSION: (b p q) r s  ≡  b (p r s) (q r s)",
        "en": "IF-FUSION: (b p q) r s  ≡  b (p r s) (q r s)",
    },
    "prove.fusion.rule_text": {
        "pl": (
            "Rozbijamy formułę po każdej zmiennej: jedna gałąź dla TRUE, druga "
            "dla FALSE. Gdy obie gałęzie dają ten sam wynik, łączą się przez "
            "IF-FUSION. Dla tautologii wszystkie liście drzewa dają TRUE."
        ),
        "en": (
            "We split the formula on each variable: one branch for TRUE, another "
            "for FALSE. When both branches yield the same result they merge via "
            "IF-FUSION. For a tautology every leaf of the tree yields TRUE."
        ),
    },
    "prove.fusion.rule_title": {
        "pl": "Reguła i strategia",
        "en": "Rule and strategy",
    },
    "prove.fusion.tree_root": {
        "pl": "[brand]Ekspansja Shannona + IF-FUSION[/brand]",
        "en": "[brand]Shannon expansion + IF-FUSION[/brand]",
    },
    "prove.fusion.kind.taut": {"pl": "tautologia", "en": "tautology"},
    "prove.fusion.kind.equiv": {"pl": "równoważność", "en": "equivalence"},
    # We use lowercase Polish "instrumental" forms in original; in EN we keep them straight.
    "prove.fusion.is_a.taut": {
        "pl": "tautologią",
        "en": "a tautology",
    },
    "prove.fusion.is_a.equiv": {
        "pl": "równoważnością",
        "en": "an equivalence",
    },
    "prove.fusion.ok_msg": {
        "pl": (
            "✓ Wszystkie gałęzie drzewa dały TRUE. IF-FUSION domknął dowód:\n"
            "[brand]{title}[/brand] jest [ok]{kind}[/ok]. [ok]QED[/ok]."
        ),
        "en": (
            "✓ Every branch of the tree yielded TRUE. IF-FUSION closed the proof:\n"
            "[brand]{title}[/brand] is [ok]{kind}[/ok]. [ok]QED[/ok]."
        ),
    },
    "prove.fusion.ok_title": {
        "pl": "Dowód IF-FUSION",
        "en": "IF-FUSION proof",
    },
    "prove.fusion.fail_msg": {
        "pl": "✗ Wszystkie gałęzie dały FALSE — formuła jest sprzeczna.",
        "en": "✗ Every branch yielded FALSE — the formula is contradictory.",
    },
    "prove.fusion.fail_title.taut": {
        "pl": "Nie jest tautologią",
        "en": "Not a tautology",
    },
    "prove.fusion.fail_title.equiv": {
        "pl": "Nie jest równoważnością",
        "en": "Not an equivalence",
    },
    "prove.fusion.partial_msg.taut": {
        "pl": (
            "⚠ Redukcja zatrzymała się na drzewie IfTree — istnieją "
            "wartościowania dające różne wyniki. [warn]Nie jest tautologią.[/warn]"
        ),
        "en": (
            "⚠ Reduction stopped at an IfTree — there exist "
            "assignments giving different results. [warn]Not a tautology.[/warn]"
        ),
    },
    "prove.fusion.partial_msg.equiv": {
        "pl": (
            "⚠ Redukcja zatrzymała się na drzewie IfTree — istnieją "
            "wartościowania dające różne wyniki. [warn]Nie jest równoważnością.[/warn]"
        ),
        "en": (
            "⚠ Reduction stopped at an IfTree — there exist "
            "assignments giving different results. [warn]Not an equivalence.[/warn]"
        ),
    },
    "prove.fusion.partial_title": {
        "pl": "Brak pełnej fuzji",
        "en": "No full fusion",
    },

    # ---- λ-parser errors (raised from parser.py) ----
    "parser.unexpected_char": {
        "pl": "Nieoczekiwany znak {ch!r} na pozycji {pos}",
        "en": "Unexpected character {ch!r} at position {pos}",
    },
    "parser.expected_kind": {
        "pl": "Oczekiwano {expected}, otrzymano {got_kind} ({got_text!r})",
        "en": "Expected {expected}, got {got_kind} ({got_text!r})",
    },
    "parser.unexpected_token": {
        "pl": "Nieoczekiwany token {kind} ({text!r})",
        "en": "Unexpected token {kind} ({text!r})",
    },
    "parser.lambda_needs_var": {
        "pl": "Po λ musi wystąpić przynajmniej jedna zmienna",
        "en": "λ must be followed by at least one variable",
    },
    "parser.expected_eof": {
        "pl": "Oczekiwano końca wyrażenia, pozostało {rest!r}",
        "en": "Expected end of expression, remaining: {rest!r}",
    },

    # ---- Church errors ----
    "church.numeral_negative": {
        "pl": "Liczby Churcha są nieujemne",
        "en": "Church numerals must be non-negative",
    },

    # ---- Lean LSP server errors ----
    "lean_server.lsp_timeout": {
        "pl": "Żądanie LSP {method} przekroczyło {timeout}s",
        "en": "LSP request {method} exceeded {timeout}s",
    },

    # ---- prove: parser errors (raised from prover.py) ----
    "prover.parser.unexpected_char": {
        "pl": "Nieoczekiwany znak {ch!r} w pozycji {pos}",
        "en": "Unexpected character {ch!r} at position {pos}",
    },
    "prover.parser.expected_token": {
        "pl": "Oczekiwano {expected}, otrzymano {got!r}",
        "en": "Expected {expected}, got {got!r}",
    },
    "prover.parser.extra_tokens": {
        "pl": "Nadmiarowe tokeny: {tokens}",
        "en": "Extra tokens: {tokens}",
    },
    "prover.parser.unexpected_eof": {
        "pl": "Nieoczekiwany koniec wyrażenia",
        "en": "Unexpected end of expression",
    },
    "prover.parser.expected_atom": {
        "pl": "Oczekiwano atomu, otrzymano {got!r}",
        "en": "Expected an atom, got {got!r}",
    },
    "prover.eval.not_boolean": {
        "pl": "Term nie zredukował się do booleana: {term}",
        "en": "Term did not reduce to a boolean: {term}",
    },

    # ---- prove: catalogue of theorems (titles + commentary) ----
    "prover.thm.demorgan1.title": {
        "pl": "Prawo De Morgana I",
        "en": "De Morgan's Law I",
    },
    "prover.thm.demorgan1.commentary": {
        "pl": (
            "Klasyczne prawo De Morgana. Negacja koniunkcji jest alternatywą "
            "negacji. Nazwane na cześć Augustusa De Morgana (1806–1871)."
        ),
        "en": (
            "The classical De Morgan law. The negation of a conjunction equals "
            "the disjunction of the negations. Named after Augustus De Morgan "
            "(1806–1871)."
        ),
    },
    "prover.thm.demorgan2.title": {
        "pl": "Prawo De Morgana II",
        "en": "De Morgan's Law II",
    },
    "prover.thm.demorgan2.commentary": {
        "pl": (
            "Druga postać prawa De Morgana: negacja alternatywy to koniunkcja "
            "negacji. Razem z pierwszym prawem tworzą parę dualną."
        ),
        "en": (
            "The second form of De Morgan's law: the negation of a disjunction "
            "is the conjunction of the negations. Together with the first law "
            "they form a dual pair."
        ),
    },
    "prover.thm.double_neg.title": {
        "pl": "Podwójne przeczenie",
        "en": "Double negation",
    },
    "prover.thm.double_neg.commentary": {
        "pl": (
            "W logice klasycznej dwie negacje się znoszą. W logice "
            "intuicjonistycznej już niekoniecznie — zobacz ćwiczenia."
        ),
        "en": (
            "In classical logic two negations cancel out. In intuitionistic "
            "logic this is not necessarily the case — see the exercises."
        ),
    },
    "prover.thm.idempotent_and.title": {
        "pl": "Idempotentność koniunkcji",
        "en": "Idempotence of conjunction",
    },
    "prover.thm.idempotent_and.commentary": {
        "pl": "A w koniunkcji z samym sobą to wciąż A.",
        "en": "A conjoined with itself is still A.",
    },
    "prover.thm.idempotent_or.title": {
        "pl": "Idempotentność alternatywy",
        "en": "Idempotence of disjunction",
    },
    "prover.thm.idempotent_or.commentary": {
        "pl": "A w alternatywie z samym sobą to wciąż A.",
        "en": "A disjoined with itself is still A.",
    },
    "prover.thm.commutative_and.title": {
        "pl": "Przemienność koniunkcji",
        "en": "Commutativity of conjunction",
    },
    "prover.thm.commutative_and.commentary": {
        "pl": "Kolejność argumentów koniunkcji nie ma znaczenia.",
        "en": "The order of the arguments of a conjunction does not matter.",
    },
    "prover.thm.associative_and.title": {
        "pl": "Łączność koniunkcji",
        "en": "Associativity of conjunction",
    },
    "prover.thm.associative_and.commentary": {
        "pl": "Sposób nawiasowania trzech koniunkcji nie ma znaczenia.",
        "en": "How a triple conjunction is parenthesised does not matter.",
    },
    "prover.thm.distrib_and_or.title": {
        "pl": "Dystrybutywność ∧ nad ∨",
        "en": "Distributivity of ∧ over ∨",
    },
    "prover.thm.distrib_and_or.commentary": {
        "pl": (
            "Podstawowe prawo rachunku propozycjonalnego; analog "
            "dystrybutywności mnożenia nad dodawaniem."
        ),
        "en": (
            "A fundamental law of propositional calculus; analogous to the "
            "distributivity of multiplication over addition."
        ),
    },
    "prover.thm.absorption.title": {
        "pl": "Pochłanianie",
        "en": "Absorption",
    },
    "prover.thm.absorption.commentary": {
        "pl": (
            "Jeśli A jest prawdą, cała alternatywa również; koniunkcja z A "
            "redukuje wszystko do A."
        ),
        "en": (
            "If A is true the whole disjunction is too; the conjunction with A "
            "collapses everything back to A."
        ),
    },
    "prover.thm.implication_def.title": {
        "pl": "Definicja implikacji",
        "en": "Definition of implication",
    },
    "prover.thm.implication_def.commentary": {
        "pl": (
            "Klasyczna redukcja implikacji do alternatywy z negacją. "
            "Kluczowa zależność między ⇒ a ∨."
        ),
        "en": (
            "The classical reduction of implication to a disjunction with a "
            "negation. A key relationship between ⇒ and ∨."
        ),
    },
    "prover.thm.contraposition.title": {
        "pl": "Kontrapozycja",
        "en": "Contraposition",
    },
    "prover.thm.contraposition.commentary": {
        "pl": (
            'Zdanie „jeżeli A, to B" jest równoważne ze zdaniem '
            '„jeżeli nie B, to nie A". Podstawowa technika dowodowa.'
        ),
        "en": (
            'The sentence "if A then B" is equivalent to the sentence '
            '"if not B then not A". A fundamental proof technique.'
        ),
    },
    "prover.thm.excluded_middle.title": {
        "pl": "Prawo wyłączonego środka",
        "en": "Law of excluded middle",
    },
    "prover.thm.excluded_middle.commentary": {
        "pl": (
            "Fundament logiki klasycznej: każde zdanie jest prawdziwe "
            "albo fałszywe. Tu formuła jest tautologią (zawsze TRUE)."
        ),
        "en": (
            "The cornerstone of classical logic: every sentence is either "
            "true or false. Here the formula is a tautology (always TRUE)."
        ),
    },
    "prover.thm.modus_ponens.title": {
        "pl": "Modus ponens (jako tautologia)",
        "en": "Modus ponens (as a tautology)",
    },
    "prover.thm.modus_ponens.commentary": {
        "pl": (
            "Gdy mamy A i A ⇒ B, możemy wywnioskować B. Najstarsza "
            "reguła wnioskowania; tu zapisana jako jedna tautologia."
        ),
        "en": (
            "Given A and A ⇒ B we may conclude B. The oldest rule of "
            "inference; written here as a single tautology."
        ),
    },
    "prover.thm.hilbert_s.title": {
        "pl": "Aksjomat S Hilberta",
        "en": "Hilbert's axiom S",
    },
    "prover.thm.hilbert_s.commentary": {
        "pl": (
            "Jeden z podstawowych aksjomatów rachunku Hilberta. "
            "W rachunku λ odpowiada kombinatorowi S."
        ),
        "en": (
            "One of the basic axioms of the Hilbert calculus. In the lambda "
            "calculus it corresponds to the S combinator."
        ),
    },
    "prove.custom.user_supplied": {
        "pl": "Wprowadzone twierdzenie",
        "en": "User-supplied theorem",
    },

    # ---- alligators (lab/alligators.py) ----
    "alligators.hungry": {
        "pl": "🐊 głodny «{param}»",
        "en": "🐊 hungry «{param}»",
    },
    "alligators.eat_arrow": {
        "pl": "⇣ jedzenie ⇣",
        "en": "⇣ feeding ⇣",
    },
    "alligators.family": {
        "pl": "🐊 rodzina (aplikacja)",
        "en": "🐊 family (application)",
    },

    # ---- lean command ----
    "lean.no_trace": {
        "pl": "Brak zapisanego śladu dla {demo}.",
        "en": "No saved trace for {demo}.",
    },
    "lean.trace_title": {
        "pl": "Ślad tactic state — {demo}",
        "en": "Tactic-state trace — {demo}",
    },
    "lean.run_failed": {
        "pl": "Nie udało się uruchomić Leana: {error}. Pokażę tylko źródło.",
        "en": "Could not run Lean: {error}. I'll only show the source.",
    },
    "lean.exit_ok": {
        "pl": "Lean zakończył się sukcesem (exit=0)",
        "en": "Lean finished successfully (exit=0)",
    },
    "lean.exit_fail": {
        "pl": "Lean zakończył się kodem {code}",
        "en": "Lean finished with code {code}",
    },
    "lean.empty_output": {
        "pl": "(brak wyjścia — pliki skompilowały się czysto)",
        "en": "(no output — the files compiled cleanly)",
    },
    "lean.mathlib_notice_body": {
        "pl": (
            "[muted]Plik [brand]{name}[/brand] używa biblioteki "
            "[brand]Mathlib[/brand] (albo Std/Aesop).\n"
            "Goły [code]lean <plik>[/code] nie ma jej w ścieżce, więc kompilacja\n"
            "zakończyłaby się błędem [code]unknown module prefix 'Mathlib'[/code].\n\n"
            "Aby uruchomić plik, potrzebujesz projektu Lake, np.:\n\n"
            "  [brand]cd lambda_lab/proofs/lean && lake init . && lake update && "
            "lake env lean {name}[/brand]\n\n"
            "Tymczasem pokażę wcześniej przygotowany ślad tactic state.[/muted]"
        ),
        "en": (
            "[muted]The file [brand]{name}[/brand] uses the "
            "[brand]Mathlib[/brand] library (or Std/Aesop).\n"
            "Plain [code]lean <file>[/code] does not have it on the path, so compilation\n"
            "would fail with [code]unknown module prefix 'Mathlib'[/code].\n\n"
            "To run the file, you need a Lake project, e.g.:\n\n"
            "  [brand]cd lambda_lab/proofs/lean && lake init . && lake update && "
            "lake env lean {name}[/brand]\n\n"
            "For now, I'll show the pre-recorded tactic-state trace.[/muted]"
        ),
    },
    "lean.mathlib_notice_title": {
        "pl": "Plik wymaga Mathlib — pomijam kompilację",
        "en": "File requires Mathlib — skipping compilation",
    },
    "lean.unknown_demo": {
        "pl": "Nieznane demo: {demo}. Dostępne: {available}",
        "en": "Unknown demo: {demo}. Available: {available}",
    },
    "lean.no_file": {
        "pl": "Brak pliku {path}. Zostawiam tylko ślad.",
        "en": "Missing file {path}. Showing the trace only.",
    },
    "lean.live": {
        "pl": "Lean jest dostępny — uruchamiam na żywo…",
        "en": "Lean is available — running live…",
    },
    "lean.unavailable": {
        "pl": "Lean niedostępny — pokażę wcześniej przygotowany ślad.",
        "en": "Lean unavailable — showing the pre-recorded trace.",
    },

    # ---- ag command ----
    "ag.empty_dir": {
        "pl": "Brak zapisanych dowodów AG w lambda_lab/proofs/alphageometry",
        "en": "No saved AG proofs in lambda_lab/proofs/alphageometry",
    },
    "ag.demos.title": {
        "pl": "Dostępne demo",
        "en": "Available demos",
    },
    "ag.col.name": {"pl": "nazwa", "en": "name"},
    "ag.col.file": {"pl": "plik", "en": "file"},
    "ag.unknown_demo": {
        "pl": "Nieznane demo: {demo}. Dostępne: {available}",
        "en": "Unknown demo: {demo}. Available: {available}",
    },
    "ag.problem": {"pl": "Problem", "en": "Problem"},
    "ag.diagram": {"pl": "Diagram", "en": "Diagram"},
    "ag.aux": {"pl": "Auxiliary construction (LM)", "en": "Auxiliary construction (LM)"},
    "ag.step": {"pl": "Krok DD+AR #{i}", "en": "DD+AR step #{i}"},
    "ag.next_prompt": {
        "pl": "ENTER → następny krok…",
        "en": "ENTER → next step…",
    },
    "ag.interrupted": {"pl": "Przerwano.", "en": "Interrupted."},
    "ag.conclusion": {"pl": "Konkluzja", "en": "Conclusion"},

    # ---- aristotle command ----
    "arist.offline.cant_reach": {
        "pl": "Nie udało się dotrzeć do [bold]{kind}[/bold] — brak sieci?",
        "en": "Could not reach [bold]{kind}[/bold] — no network?",
    },
    "arist.offline.works_header": {
        "pl": "[bold]Co DZIAŁA bez internetu:[/bold]",
        "en": "[bold]What WORKS without the internet:[/bold]",
    },
    "arist.offline.works.1": {
        "pl": "  • arist show/compile/export/pdf/log/history — pracują na lokalnym cache",
        "en": "  • arist show/compile/export/pdf/log/history — work on the local cache",
    },
    "arist.offline.works.2": {
        "pl": "  • arist compile --server / --cache — Lean LSP / lake build lokalnie",
        "en": "  • arist compile --server / --cache — Lean LSP / lake build locally",
    },
    "arist.offline.works.3": {
        "pl": "  • arist warmup — rozgrzewka Mathliba",
        "en": "  • arist warmup — Mathlib warm-up",
    },
    "arist.offline.works.4": {
        "pl": "  • Wszystkie komendy λ-calculus (reduce, church, peano, alligators, prove, tour, quiz)",
        "en": "  • All λ-calculus commands (reduce, church, peano, alligators, prove, tour, quiz)",
    },
    "arist.offline.works.5": {
        "pl": "  • lean <demo> (legacy, Lean 4.24 + offline trace)",
        "en": "  • lean <demo> (legacy, Lean 4.24 + offline trace)",
    },
    "arist.offline.works.6": {
        "pl": "  • ag <demo> (AlphaGeometry replay)",
        "en": "  • ag <demo> (AlphaGeometry replay)",
    },
    "arist.offline.cached_header": {
        "pl": "[bold]Twoje ostatnio pobrane projekty Aristotle'a (lokalny cache):[/bold]",
        "en": "[bold]Your most recent Aristotle projects (local cache):[/bold]",
    },
    "arist.offline.cached_hint": {
        "pl": "Pobaw się nimi: `arist show <id>`, `arist compile --server <id>`, `arist pdf <id>`.",
        "en": "Have a play: `arist show <id>`, `arist compile --server <id>`, `arist pdf <id>`.",
    },
    "arist.offline.raw_msg": {
        "pl": "[muted]Surowy komunikat: {short}[/muted]",
        "en": "[muted]Raw message: {short}[/muted]",
    },
    "arist.offline.title": {
        "pl": "Tryb offline",
        "en": "Offline mode",
    },
    "arist.no_cli": {
        "pl": "Brak CLI `aristotle`. Zainstaluj: `uv tool install aristotlelib` lub `pip install aristotlelib`.",
        "en": "No `aristotle` CLI. Install with: `uv tool install aristotlelib` or `pip install aristotlelib`.",
    },
    "arist.no_key.body": {
        "pl": (
            "Brak klucza API.\n\n"
            "Utwórz plik [bold]{path}[/bold] zawierający:\n"
            "[dim]ARISTOTLE_API_KEY=sk-…[/dim]\n\n"
            "Następnie uruchom ponownie λambda Lab. Klucz zostanie wczytany automatycznie."
        ),
        "en": (
            "No API key.\n\n"
            "Create the file [bold]{path}[/bold] containing:\n"
            "[dim]ARISTOTLE_API_KEY=sk-…[/dim]\n\n"
            "Then restart λambda Lab. The key will be loaded automatically."
        ),
    },
    "arist.no_key.title": {
        "pl": "Aristotle",
        "en": "Aristotle",
    },
    "arist.submit.usage": {
        "pl": "Użycie:",
        "en": "Usage:",
    },
    "arist.submit.usage_msg": {
        "pl": "arist submit \"<prompt>\" [--project-dir PATH] [--wait]",
        "en": "arist submit \"<prompt>\" [--project-dir PATH] [--wait]",
    },
    "arist.no_output": {
        "pl": "brak wyjścia",
        "en": "no output",
    },
    "arist.submit.err_title": {
        "pl": "Aristotle submit — błąd",
        "en": "Aristotle submit — error",
    },
    "arist.submit.no_id_title": {
        "pl": "Aristotle odpowiedział, ale nie znalazłem project_id",
        "en": "Aristotle responded, but I couldn't find project_id",
    },
    "arist.submit.ok_body": {
        "pl": (
            "[bold]project_id:[/bold] {project_id}\n"
            "[dim]prompt:[/dim] {prompt}\n\n"
            "Śledzenie: [bold]arist watch {project_id}[/bold]\n"
            "Lista:    [bold]arist list[/bold]"
        ),
        "en": (
            "[bold]project_id:[/bold] {project_id}\n"
            "[dim]prompt:[/dim] {prompt}\n\n"
            "Track:  [bold]arist watch {project_id}[/bold]\n"
            "List:   [bold]arist list[/bold]"
        ),
    },
    "arist.submit.ok_title": {
        "pl": "Wysłane do Aristotle'a",
        "en": "Sent to Aristotle",
    },
    "arist.list.err_title": {
        "pl": "arist list",
        "en": "arist list",
    },
    "arist.list.title": {
        "pl": "Projekty Aristotle'a",
        "en": "Aristotle projects",
    },
    "arist.list.col.id": {"pl": "project_id", "en": "project_id"},
    "arist.list.col.status": {"pl": "status", "en": "status"},
    "arist.list.col.created": {"pl": "utworzone", "en": "created"},
    "arist.list.col.prompt": {"pl": "prompt", "en": "prompt"},
    "arist.spinner.interrupted": {
        "pl": "Przerwano (Ctrl-C).",
        "en": "Interrupted (Ctrl-C).",
    },
    "arist.watch.usage": {
        "pl": "arist watch <project_id>",
        "en": "arist watch <project_id>",
    },
    "arist.watch.polling": {
        "pl": "Polling Aristotle'a co 10 s — Ctrl-C przerywa.",
        "en": "Polling Aristotle every 10 s — Ctrl-C aborts.",
    },
    "arist.watch.interrupted": {
        "pl": "Przerwano oczekiwanie (Ctrl-C).",
        "en": "Wait interrupted (Ctrl-C).",
    },
    "arist.watch.err_title": {
        "pl": "arist watch",
        "en": "arist watch",
    },
    "arist.watch.saved_in": {
        "pl": "Rozwiązanie zapisane w: [bold]{dest}[/bold]",
        "en": "Solution saved in: [bold]{dest}[/bold]",
    },
    "arist.watch.lean_files": {
        "pl": "\nPliki [bold].lean[/bold] ({count}):",
        "en": "\n[bold].lean[/bold] files ({count}):",
    },
    "arist.watch.next_steps": {
        "pl": (
            "\nZobacz:       [bold]arist show {project_id}[/bold]\n"
            "Skompiluj:    [bold]arist compile {project_id}[/bold]\n"
            "Informalizuj: [bold]arist informal {project_id}[/bold]"
        ),
        "en": (
            "\nView:        [bold]arist show {project_id}[/bold]\n"
            "Compile:     [bold]arist compile {project_id}[/bold]\n"
            "Informalize: [bold]arist informal {project_id}[/bold]"
        ),
    },
    "arist.watch.done_title": {
        "pl": "Gotowe",
        "en": "Done",
    },
    "arist.result.usage": {
        "pl": "arist result <project_id>",
        "en": "arist result <project_id>",
    },
    "arist.result.err_title": {
        "pl": "arist result",
        "en": "arist result",
    },
    "arist.result.fetched": {
        "pl": "[ok]Pobrane:[/ok] {total} plików, w tym {lean} .lean. Dalej: [bold]arist show {project_id}[/bold].",
        "en": "[ok]Fetched:[/ok] {total} files, including {lean} .lean. Next: [bold]arist show {project_id}[/bold].",
    },
    "arist.show.usage": {
        "pl": "arist show <project_id>",
        "en": "arist show <project_id>",
    },
    "arist.show.no_files": {
        "pl": "Brak plików .lean w {dest}. Najpierw: arist watch {project_id}",
        "en": "No .lean files in {dest}. First run: arist watch {project_id}",
    },
    "arist.compile.usage": {
        "pl": "arist compile <project_id> [--cache] [--server]",
        "en": "arist compile <project_id> [--cache] [--server]",
    },
    "arist.compile.no_id": {
        "pl": "Brak project_id.",
        "en": "Missing project_id.",
    },
    "arist.compile.no_files": {
        "pl": "Brak plików .lean. Najpierw: arist watch {project_id}",
        "en": "No .lean files. First run: arist watch {project_id}",
    },
    "arist.compile.no_lake_body": {
        "pl": (
            "Brak projektu Lake dla Aristotle'a.\n\n"
            "Spodziewana ścieżka: [bold]{path}[/bold]\n"
            "Utwórz go (Mathlib v4.28.0) albo poczekaj na zakończenie setupu."
        ),
        "en": (
            "No Lake project for Aristotle.\n\n"
            "Expected path: [bold]{path}[/bold]\n"
            "Create it (Mathlib v4.28.0) or wait for setup to finish."
        ),
    },
    "arist.compile.no_lake_title": {
        "pl": "lean_aristotle/ nie istnieje",
        "en": "lean_aristotle/ does not exist",
    },
    "arist.compile.modes_hint": {
        "pl": (
            "[muted]Wskazówka: `arist compile --server` trzyma Lean server w pamięci "
            "(Mathlib ładuje się raz na sesję); `--cache` kopiuje plik do biblioteki "
            "i używa `lake build` (następny raz jest natychmiastowy). "
            "Domyślny tryb — świeży proces Lean — jest najwolniejszy.[/muted]"
        ),
        "en": (
            "[muted]Hint: `arist compile --server` keeps the Lean server in memory "
            "(Mathlib loads once per session); `--cache` copies the file into the library "
            "and uses `lake build` (the next time it is instant). "
            "The default mode — a fresh Lean process — is the slowest.[/muted]"
        ),
    },
    "arist.compile.compiling": {
        "pl": "Kompiluję {name}",
        "en": "Compiling {name}",
    },
    "arist.compile.zero_warn": {
        "pl": "[dim]0 błędów, 0 ostrzeżeń.[/dim]",
        "en": "[dim]0 errors, 0 warnings.[/dim]",
    },
    "arist.compile.no_output_dim": {
        "pl": "[dim]brak wyjścia[/dim]",
        "en": "[dim]no output[/dim]",
    },
    "arist.compile.ok_title": {
        "pl": "✓ {name} skompilował się",
        "en": "✓ {name} compiled successfully",
    },
    "arist.compile.fail_title": {
        "pl": "✗ {name} — błąd kompilacji (exit {rc})",
        "en": "✗ {name} — compilation error (exit {rc})",
    },
    "arist.compile.no_lean_files": {
        "pl": "Brak plików .lean.",
        "en": "No .lean files.",
    },
    "arist.compile.cache_intro": {
        "pl": "Tryb --cache: kopiuję plik(i) do LambdaAristotle/Solutions/ i buduję przez lake.",
        "en": "Mode --cache: copying file(s) into LambdaAristotle/Solutions/ and building via lake.",
    },
    "arist.compile.modules_to_build": {
        "pl": "[muted]Moduły do zbudowania:[/muted] {modules}",
        "en": "[muted]Modules to build:[/muted] {modules}",
    },
    "arist.compile.cached_ok_body": {
        "pl": "[dim]Zbudowane. Następna kompilacja tego modułu będzie natychmiastowa (olean w cache).[/dim]",
        "en": "[dim]Built. The next compilation of this module will be instant (olean in cache).[/dim]",
    },
    "arist.compile.cached_ok_title": {
        "pl": "✓ {mod} skompilowany (cached)",
        "en": "✓ {mod} compiled (cached)",
    },
    "arist.compile.cached_fail_title": {
        "pl": "✗ {mod} — lake build exit {rc}",
        "en": "✗ {mod} — lake build exit {rc}",
    },
    "arist.compile.server_intro": {
        "pl": "Tryb --server: podłączam się do persistentnego Lean LSP.",
        "en": "Mode --server: connecting to the persistent Lean LSP.",
    },
    "arist.compile.server_start_fail": {
        "pl": "Nie udało się uruchomić Lean server:\n{error}",
        "en": "Could not start Lean server:\n{error}",
    },
    "arist.compile.server_title": {
        "pl": "server",
        "en": "server",
    },
    "arist.compile.server_timeout": {
        "pl": "timeout:",
        "en": "timeout:",
    },
    "arist.compile.server_lsp_err": {
        "pl": "LSP error:",
        "en": "LSP error:",
    },
    "arist.compile.server_ok_extra": {
        "pl": "[muted]czas: {elapsed:.1f} s (Mathlib trzymany w pamięci LSP)[/muted]",
        "en": "[muted]elapsed: {elapsed:.1f} s (Mathlib kept in LSP memory)[/muted]",
    },
    "arist.compile.server_ok_title": {
        "pl": "✓ {name} skompilował się (via server)",
        "en": "✓ {name} compiled (via server)",
    },
    "arist.compile.server_no_details": {
        "pl": "[dim]brak szczegółów[/dim]",
        "en": "[dim]no details[/dim]",
    },
    "arist.compile.server_fail_title": {
        "pl": "✗ {name} — {rc} błąd(ów), czas {elapsed:.1f} s",
        "en": "✗ {name} — {rc} error(s), elapsed {elapsed:.1f} s",
    },
    "arist.server.started": {
        "pl": "Lean server uruchomiony (Mathlib ładuje się w tle).",
        "en": "Lean server started (Mathlib is loading in the background).",
    },
    "arist.server.stopped": {
        "pl": "Lean server zatrzymany.",
        "en": "Lean server stopped.",
    },
    "arist.server.idle": {
        "pl": "Lean server: nie działa. `arist server start`.",
        "en": "Lean server: not running. `arist server start`.",
    },
    "arist.server.running": {
        "pl": "Lean server działa (project: {dir}).",
        "en": "Lean server is running (project: {dir}).",
    },
    "arist.server.unknown": {
        "pl": "Nieznane:",
        "en": "Unknown:",
    },
    "arist.server.usage": {
        "pl": "Użycie: arist server [start|stop|status]",
        "en": "Usage: arist server [start|stop|status]",
    },
    "arist.cancel.usage": {
        "pl": "arist cancel <project_id>",
        "en": "arist cancel <project_id>",
    },
    "arist.formalize.usage": {
        "pl": "arist formalize <plik.md|.txt>",
        "en": "arist formalize <file.md|.txt>",
    },
    "arist.formalize.no_file": {
        "pl": "Plik nie istnieje:",
        "en": "File does not exist:",
    },
    "arist.formalize.err_title": {
        "pl": "arist formalize",
        "en": "arist formalize",
    },
    "arist.formalize.queued": {
        "pl": "[ok]project_id:[/ok] {pid} — `arist watch {pid}` by śledzić.",
        "en": "[ok]project_id:[/ok] {pid} — run `arist watch {pid}` to track.",
    },
    "arist.informal.usage": {
        "pl": "arist informal <project_id>",
        "en": "arist informal <project_id>",
    },
    "arist.informal.no_files": {
        "pl": "Brak plików .lean. Najpierw: arist watch {project_id}",
        "en": "No .lean files. First run: arist watch {project_id}",
    },
    "arist.informal.no_openai_body": {
        "pl": (
            "Brak klucza OpenAI.\n\n"
            "Utwórz plik [bold]{path}[/bold]:\n"
            "[dim]OPENAI_API_KEY=sk-…\nOPENAI_MODEL=gpt-5.5-reasoning\nOPENAI_REASONING_EFFORT=high[/dim]\n\n"
            "Następnie uruchom ponownie Lambda Lab."
        ),
        "en": (
            "No OpenAI key.\n\n"
            "Create the file [bold]{path}[/bold]:\n"
            "[dim]OPENAI_API_KEY=sk-…\nOPENAI_MODEL=gpt-5.5-reasoning\nOPENAI_REASONING_EFFORT=high[/dim]\n\n"
            "Then restart Lambda Lab."
        ),
    },
    "arist.informal.no_openai_title": {
        "pl": "OpenAI — informalizacja niedostępna",
        "en": "OpenAI — informalization unavailable",
    },
    "arist.informal.no_lib": {
        "pl": "Brak biblioteki `openai`. `pip install openai`.",
        "en": "Missing `openai` library. Run `pip install openai`.",
    },
    "arist.informal.prompt": {
        "pl": (
            "Jesteś asystentem matematycznym dla polskich licealistów. "
            "Poniżej dowód w Lean 4 + Mathlib. "
            "Wyjaśnij go po polsku: (1) o czym jest twierdzenie (potocznie), "
            "(2) główny pomysł dowodu (1–3 zdania), (3) krok-po-kroku co robią kolejne taktyki "
            "(bullet list), (4) dlaczego to działa (1 akapit). "
            "WAŻNE: wzory ZAWSZE otaczaj znakami dolara — inline `$x^2$`, display `$$...$$`. "
            "Nie używaj `\\(...\\)` ani `\\[...\\]`. Każde `\\operatorname{{}}`, `\\mathbb{{}}`, "
            "`\\frac{{}}` itp. MUSI być wewnątrz dolarów. Nie nadużywaj żargonu.\n\n"
            "```lean\n{text}\n```"
        ),
        "en": (
            "You are a mathematics assistant for high-school students. "
            "Below is a proof in Lean 4 + Mathlib. "
            "Explain it in plain English: (1) what the theorem is about (informally), "
            "(2) the main idea of the proof (1-3 sentences), (3) step-by-step what each tactic does "
            "(bullet list), (4) why it works (one paragraph). "
            "IMPORTANT: ALWAYS wrap formulas in dollar signs — inline `$x^2$`, display `$$...$$`. "
            "Do NOT use `\\(...\\)` or `\\[...\\]`. Every `\\operatorname{{}}`, `\\mathbb{{}}`, "
            "`\\frac{{}}` etc. MUST sit inside dollars. Avoid jargon.\n\n"
            "```lean\n{text}\n```"
        ),
    },
    "arist.informal.requesting": {
        "pl": "→ OpenAI {model} (effort={effort}) — {name}",
        "en": "→ OpenAI {model} (effort={effort}) — {name}",
    },
    "arist.informal.offline_kind": {
        "pl": "OpenAI (informalizacja)",
        "en": "OpenAI (informalization)",
    },
    "arist.informal.model_not_found_body": {
        "pl": (
            "Model [bold]{model}[/bold] jest niedostępny dla Twojego konta.\n\n"
            "Dostępne modele (skrót):\n{hint}\n\n"
            "Zmień [bold]OPENAI_MODEL[/bold] w {path}."
        ),
        "en": (
            "Model [bold]{model}[/bold] is not available for your account.\n\n"
            "Available models (sample):\n{hint}\n\n"
            "Change [bold]OPENAI_MODEL[/bold] in {path}."
        ),
    },
    "arist.informal.model_not_found_title": {
        "pl": "OpenAI — model_not_found",
        "en": "OpenAI — model_not_found",
    },
    "arist.informal.openai_err": {
        "pl": "OpenAI: {msg}",
        "en": "OpenAI: {msg}",
    },
    "arist.informal.panel_title": {
        "pl": "Informalizacja — {name} (model: {model})",
        "en": "Informalization — {name} (model: {model})",
    },
    "arist.export.usage": {
        "pl": "arist export <project_id>",
        "en": "arist export <project_id>",
    },
    "arist.export.no_files": {
        "pl": "Brak plików .lean w {dest}. Najpierw: arist watch {project_id}",
        "en": "No .lean files in {dest}. First run: arist watch {project_id}",
    },
    "arist.export.composing": {
        "pl": "Składam report.md → PDF…",
        "en": "Building report.md → PDF…",
    },
    "arist.export.markdown_path": {
        "pl": "[muted]Markdown źródłowy: {path}[/muted]",
        "en": "[muted]Markdown source: {path}[/muted]",
    },
    "arist.export.ok_body": {
        "pl": (
            "Plik źródłowy: [bold]{md}[/bold]\n"
            "PDF:           [bold]{pdf}[/bold]\n\n"
            "Podgląd: [bold]arist pdf {project_id}[/bold]"
        ),
        "en": (
            "Source file: [bold]{md}[/bold]\n"
            "PDF:         [bold]{pdf}[/bold]\n\n"
            "Preview: [bold]arist pdf {project_id}[/bold]"
        ),
    },
    "arist.export.ok_title": {
        "pl": "Export LaTeX → PDF gotowy",
        "en": "LaTeX → PDF export ready",
    },
    "arist.pdf.usage": {
        "pl": "arist pdf <project_id>",
        "en": "arist pdf <project_id>",
    },
    "arist.pdf.no_files": {
        "pl": "Brak plików .lean. Najpierw: arist watch {project_id}",
        "en": "No .lean files. First run: arist watch {project_id}",
    },
    "arist.pdf.no_openai_body": {
        "pl": (
            "Brak OPENAI_API_KEY — nie mogę wygenerować informalizacji.\n"
            "Uzupełnij ~/.config/openai/env albo uruchom `arist export <id>` "
            "(eksport bez informalizacji, tylko Lean)."
        ),
        "en": (
            "No OPENAI_API_KEY — I cannot generate the informalization.\n"
            "Fill in ~/.config/openai/env or run `arist export <id>` "
            "(export without informalization, only Lean)."
        ),
    },
    "arist.pdf.no_openai_title": {
        "pl": "arist pdf",
        "en": "arist pdf",
    },
    "arist.pdf.no_pandoc_body": {
        "pl": "Brak [bold]pandoc[/]. Zainstaluj: `brew install pandoc`.",
        "en": "No [bold]pandoc[/]. Install with: `brew install pandoc`.",
    },
    "arist.pdf.no_pandoc_title": {
        "pl": "export PDF",
        "en": "export PDF",
    },
    "arist.pdf.no_engine_body": {
        "pl": "Brak silnika LaTeX (xelatex/pdflatex). Zainstaluj MacTeX/BasicTeX.",
        "en": "No LaTeX engine (xelatex/pdflatex). Install MacTeX/BasicTeX.",
    },
    "arist.pdf.spinner": {
        "pl": "pandoc → {engine} → PDF",
        "en": "pandoc → {engine} → PDF",
    },
    "arist.pdf.engine_fail_title": {
        "pl": "pandoc/{engine} exit {rc}",
        "en": "pandoc/{engine} exit {rc}",
    },
    "arist.pdf.open_manual": {
        "pl": "[muted]Otwórz ręcznie:[/muted] {path}",
        "en": "[muted]Open manually:[/muted] {path}",
    },
    "arist.pdf.opened": {
        "pl": "Otwarto podgląd:",
        "en": "Preview opened:",
    },
    "arist.warmup.no_lake": {
        "pl": "Brak projektu Lake.",
        "en": "No Lake project.",
    },
    "arist.warmup.no_file": {
        "pl": "Brak pliku prewarm: {path}",
        "en": "No prewarm file: {path}",
    },
    "arist.warmup.starting": {
        "pl": "Rozgrzewam cache Mathliba (ok. 10-15 s pierwszy raz, potem natychmiast).",
        "en": "Warming up the Mathlib cache (about 10-15 s the first time, then instant).",
    },
    "arist.warmup.spinner": {
        "pl": "Ładuję Mathlib.Tactic do page cache",
        "en": "Loading Mathlib.Tactic into the page cache",
    },
    "arist.warmup.ok_body": {
        "pl": (
            "Rozgrzewka zakończona w [bold]{elapsed:.1f} s[/bold].\n"
            "Od teraz kompilacja plików z `import Mathlib.*` jest ~3-4x szybsza "
            "dopóki system nie wyrzuci oleanów z page cache."
        ),
        "en": (
            "Warm-up finished in [bold]{elapsed:.1f} s[/bold].\n"
            "From now on, compilation of files with `import Mathlib.*` is ~3-4x faster "
            "until the system evicts the oleans from the page cache."
        ),
    },
    "arist.warmup.ok_title": {
        "pl": "cache Mathliba rozgrzany",
        "en": "Mathlib cache warmed up",
    },
    "arist.warmup.fail_title": {
        "pl": "warmup — exit {rc}",
        "en": "warmup — exit {rc}",
    },
    "arist.log.bad_limit": {
        "pl": "--limit oczekuje liczby, dostało:",
        "en": "--limit expects a number, got:",
    },
    "arist.log.empty": {
        "pl": "Brak wpisów w dzienniku.",
        "en": "No entries in the log.",
    },
    "arist.log.title": {
        "pl": "Dziennik Lambda Lab (ostatnie {count})",
        "en": "Lambda Lab log (last {count})",
    },
    "arist.log.col.time": {"pl": "czas", "en": "time"},
    "arist.log.col.kind": {"pl": "kind", "en": "kind"},
    "arist.log.col.project": {"pl": "project", "en": "project"},
    "arist.log.col.details": {"pl": "szczegóły", "en": "details"},
    "arist.demo.body": {
        "pl": (
            "[bold]Przykład z wykładu „Wtyczki, kable i krokodyle”.[/bold]\n\n"
            "[dim]prompt:[/dim] {prompt}\n\n"
            "Wysyłam do Aristotle'a. Potem: "
            "[bold]arist watch <id>[/bold] → [bold]arist compile <id>[/bold] → "
            "[bold]arist informal <id>[/bold]."
        ),
        "en": (
            "[bold]Example from the lecture \"Plugs, cables and crocodiles\".[/bold]\n\n"
            "[dim]prompt:[/dim] {prompt}\n\n"
            "Sending to Aristotle. Then: "
            "[bold]arist watch <id>[/bold] → [bold]arist compile <id>[/bold] → "
            "[bold]arist informal <id>[/bold]."
        ),
    },
    "arist.demo.title": {
        "pl": "arist demo — De Morgan",
        "en": "arist demo — De Morgan",
    },
    "arist.key.set": {"pl": "ustawiony", "en": "set"},
    "arist.key.missing": {"pl": "BRAK", "en": "MISSING"},
    "arist.key.body": {
        "pl": (
            "ARISTOTLE_API_KEY: [bold]{ar}[/bold] (plik: {arist_env})\n"
            "OPENAI_API_KEY:    [bold]{oa}[/bold] (plik: {openai_env})\n"
            "  model:   {model}\n"
            "  effort:  {effort}\n\n"
            "Projekt Lake: {lake}\n"
            "Historia:     {jobs}"
        ),
        "en": (
            "ARISTOTLE_API_KEY: [bold]{ar}[/bold] (file: {arist_env})\n"
            "OPENAI_API_KEY:    [bold]{oa}[/bold] (file: {openai_env})\n"
            "  model:   {model}\n"
            "  effort:  {effort}\n\n"
            "Lake project: {lake}\n"
            "History:      {jobs}"
        ),
    },
    "arist.key.title": {
        "pl": "Status kluczy",
        "en": "Key status",
    },
    "arist.help.body": {
        "pl": (
            "[bold]arist[/bold] — integracja z Aristotle (Harmonic AI).\n\n"
            "Podkomendy:\n"
            "  [accent]submit[/accent]   \"<prompt>\"  — wyślij zadanie do Aristotle'a\n"
            "  [accent]list[/accent]     [--status …]  — historia projektów\n"
            "  [accent]watch[/accent]    <id>           — czekaj i ściągnij rozwiązanie\n"
            "  [accent]result[/accent]   <id>           — jednorazowe pobranie\n"
            "  [accent]show[/accent]     <id>           — wyświetl .lean\n"
            "  [accent]compile[/accent]  <id> [--cache|--server]\n"
            "                              — --cache: lake build + olean reuse\n"
            "                              — --server: persistent Lean LSP (Mathlib 1x)\n"
            "  [accent]cancel[/accent]   <id>           — anuluj projekt\n"
            "  [accent]formalize[/accent] <plik>        — nieformalny tekst → Lean\n"
            "  [accent]informal[/accent] <id>           — GPT wyjaśnia dowód po polsku\n"
            "  [accent]export[/accent]   <id>           — report.md + report.pdf (pandoc + xelatex)\n"
            "  [accent]pdf[/accent]      <id>           — informal → export → otwórz podgląd PDF\n"
            "  [accent]log[/accent]      [--limit N]    — dziennik Twoich interakcji (persystentny)\n"
            "  [accent]warmup[/accent]                  — rozgrzej cache Mathliba (3-4x szybszy compile)\n"
            "  [accent]server[/accent]   [start|stop|status] — zarządzaj persistentnym Lean LSP\n"
            "  [accent]demo[/accent]                    — przykład z wykładu (De Morgan)\n"
            "  [accent]key[/accent]                     — status kluczy API\n\n"
            "[dim]Klucz Aristotle → ~/.config/aristotle/env\n"
            "Klucz OpenAI    → ~/.config/openai/env[/dim]"
        ),
        "en": (
            "[bold]arist[/bold] — Aristotle (Harmonic AI) integration.\n\n"
            "Subcommands:\n"
            "  [accent]submit[/accent]   \"<prompt>\"  — send a task to Aristotle\n"
            "  [accent]list[/accent]     [--status …]  — project history\n"
            "  [accent]watch[/accent]    <id>           — wait and fetch the solution\n"
            "  [accent]result[/accent]   <id>           — one-shot download\n"
            "  [accent]show[/accent]     <id>           — display .lean\n"
            "  [accent]compile[/accent]  <id> [--cache|--server]\n"
            "                              — --cache: lake build + olean reuse\n"
            "                              — --server: persistent Lean LSP (Mathlib once)\n"
            "  [accent]cancel[/accent]   <id>           — cancel a project\n"
            "  [accent]formalize[/accent] <file>        — informal text → Lean\n"
            "  [accent]informal[/accent] <id>           — GPT explains the proof informally\n"
            "  [accent]export[/accent]   <id>           — report.md + report.pdf (pandoc + xelatex)\n"
            "  [accent]pdf[/accent]      <id>           — informal → export → open the PDF preview\n"
            "  [accent]log[/accent]      [--limit N]    — log of your interactions (persistent)\n"
            "  [accent]warmup[/accent]                  — warm up the Mathlib cache (3-4x faster compile)\n"
            "  [accent]server[/accent]   [start|stop|status] — manage the persistent Lean LSP\n"
            "  [accent]demo[/accent]                    — lecture example (De Morgan)\n"
            "  [accent]key[/accent]                     — API key status\n\n"
            "[dim]Aristotle key → ~/.config/aristotle/env\n"
            "OpenAI key   → ~/.config/openai/env[/dim]"
        ),
    },
    "arist.help.title": {
        "pl": "arist",
        "en": "arist",
    },
    "arist.report.author_suffix": {
        "pl": "Lambda Lab · Aristotle (Harmonic AI) — informalizacja: {model}",
        "en": "Lambda Lab · Aristotle (Harmonic AI) — informalization: {model}",
    },
    "arist.report.lang": {
        "pl": "pl-PL",
        "en": "en-US",
    },
    "arist.report.section.task": {
        "pl": "## Zadanie\n",
        "en": "## Task\n",
    },
    "arist.report.section.informalization": {
        "pl": "Informalizacja",
        "en": "Informalization",
    },
    "arist.report.section.lean_proof": {
        "pl": "\n## Dowód w Lean 4\n",
        "en": "\n## Proof in Lean 4\n",
    },
    "arist.report.section.explanation": {
        "pl": "\n## Wyjaśnienie — informalizacja\n",
        "en": "\n## Explanation — informalization\n",
    },
    "arist.report.no_informal": {
        "pl": "_Brak informalizacji. Uruchom `arist informal <id>`._\n",
        "en": "_No informalization. Run `arist informal <id>`._\n",
    },

    "arist.argparse_err": {
        "pl": "Błąd parsowania argumentów: {error}",
        "en": "Argument parse error: {error}",
    },
    "arist.unknown_sub": {
        "pl": "Nieznana podkomenda:",
        "en": "Unknown subcommand:",
    },
    "arist.unknown_sub_hint": {
        "pl": "Wpisz `arist`, by zobaczyć listę.",
        "en": "Type `arist` to see the list.",
    },

    "help.long.arist": {
        "pl": (
            "[bold]arist <subcmd>[/bold] (także aristotle)  ·  integracja z Aristotle (Harmonic AI).\n\n"
            "Aristotle to zautomatyzowany dowodzący w Lean 4 + Mathlib (v4.28.0).\n"
            "Wysyłamy prompt, Aristotle zwraca gotowy plik .lean, my go kompilujemy\n"
            "i (opcjonalnie) prosimy GPT o wyjaśnienie dowodu po polsku.\n\n"
            "[brand]Podkomendy:[/brand]\n"
            "  arist submit \"<prompt>\"    # wyślij zadanie\n"
            "  arist list [--status IN_PROGRESS]\n"
            "  arist watch <id>            # czekaj + ściągnij po COMPLETE\n"
            "  arist result <id>           # jednorazowe pobranie\n"
            "  arist show <id>             # wyświetl .lean z podświetlaniem\n"
            "  arist compile <id>          # lake env lean … (Mathlib v4.28)\n"
            "  arist cancel <id>           # anuluj projekt\n"
            "  arist formalize <plik>      # nieformalny tekst → Lean\n"
            "  arist informal <id>         # GPT wyjaśnia dowód po polsku\n"
            "  arist demo                  # przykład z wykładu (De Morgan)\n"
            "  arist key                   # status kluczy API\n\n"
            "[brand]Klucze:[/brand]\n"
            "  ~/.config/aristotle/env  → ARISTOTLE_API_KEY=…\n"
            "  ~/.config/openai/env     → OPENAI_API_KEY=… , OPENAI_MODEL=…\n\n"
            "[brand]Typowy flow:[/brand]\n"
            "  arist demo → (zapisz project_id) → arist watch <id> →\n"
            "  arist compile <id> → arist informal <id>\n"
        ),
        "en": (
            "[bold]arist <subcmd>[/bold] (also aristotle)  ·  Aristotle (Harmonic AI) integration.\n\n"
            "Aristotle is an automated prover for Lean 4 + Mathlib (v4.28.0).\n"
            "We send a prompt, Aristotle returns a ready .lean file, we compile it\n"
            "and (optionally) ask GPT for an informal explanation of the proof.\n\n"
            "[brand]Subcommands:[/brand]\n"
            "  arist submit \"<prompt>\"    # send a task\n"
            "  arist list [--status IN_PROGRESS]\n"
            "  arist watch <id>            # wait + fetch on COMPLETE\n"
            "  arist result <id>           # one-shot download\n"
            "  arist show <id>             # display .lean with syntax highlighting\n"
            "  arist compile <id>          # lake env lean … (Mathlib v4.28)\n"
            "  arist cancel <id>           # cancel a project\n"
            "  arist formalize <file>      # informal text → Lean\n"
            "  arist informal <id>         # GPT explains the proof informally\n"
            "  arist demo                  # the lecture example (De Morgan)\n"
            "  arist key                   # API key status\n\n"
            "[brand]Keys:[/brand]\n"
            "  ~/.config/aristotle/env  → ARISTOTLE_API_KEY=…\n"
            "  ~/.config/openai/env     → OPENAI_API_KEY=… , OPENAI_MODEL=…\n\n"
            "[brand]Typical flow:[/brand]\n"
            "  arist demo → (save project_id) → arist watch <id> →\n"
            "  arist compile <id> → arist informal <id>\n"
        ),
    },

    # ---- tracing.py (β-reduction trace) ----
    "tracing.title": {"pl": "Ślad redukcji", "en": "Reduction trace"},
    "tracing.input_term": {"pl": "Term wejściowy", "en": "Input term"},
    "tracing.normal_form": {"pl": "Postać normalna ✓", "en": "Normal form ✓"},
    "tracing.stopped_after": {
        "pl": "Przerwano po {n} krokach",
        "en": "Stopped after {n} steps",
    },
    "tracing.continue": {
        "pl": "ENTER aby kontynuować…",
        "en": "Press ENTER to continue…",
    },
    "tracing.step": {"pl": "Krok {n}", "en": "Step {n}"},
    "tracing.before": {"pl": "przed", "en": "before"},
    "tracing.after": {"pl": "po", "en": "after"},
    "tracing.rule": {"pl": "reguła", "en": "rule"},

    # ---- narrator.py (pedagogical remarks during reduction) ----
    "narrator.opener.says": {"pl": "🐊 Krokodyl mówi:", "en": "🐊 The crocodile says:"},
    "narrator.opener.hungry": {
        "pl": "🐊 Głodny aligator żuje:",
        "en": "🐊 The hungry alligator chews:",
    },
    "narrator.opener.old": {
        "pl": "🐊 Stary krokodyl szepcze:",
        "en": "🐊 The old crocodile whispers:",
    },
    "narrator.beta": {
        "pl": "β-redukcja: (λ{param}. _) _  zastępuje wszystkie wystąpienia [brand]{param}[/brand] przez [accent]argument[/accent].",
        "en": "β-reduction: (λ{param}. _) _  substitutes every occurrence of [brand]{param}[/brand] with the [accent]argument[/accent].",
    },
    "narrator.alpha": {
        "pl": "α-konwersja: zmieniamy nazwę [brand]{old}[/brand] → [brand]{new}[/brand], żeby uniknąć kolizji z wolnymi zmiennymi.",
        "en": "α-conversion: rename [brand]{old}[/brand] → [brand]{new}[/brand] to avoid colliding with free variables.",
    },
    "narrator.eta": {
        "pl": "η-redukcja: (λ{param}. f {param}) ≡ f, bo owijanie funkcji w λ o tej samej nazwie nic nie zmienia.",
        "en": "η-reduction: (λ{param}. f {param}) ≡ f — wrapping a function in a λ with the same name changes nothing.",
    },
    "narrator.normal_form": {
        "pl": "Osiągnęliśmy postać normalną — nie da się już zredukować.",
        "en": "We have reached normal form — no further reduction is possible.",
    },
    "narrator.stuck": {
        "pl": "Po {steps} krokach wciąż jest redeks. Możliwe, że term nie ma postaci normalnej (np. Ω).",
        "en": "After {steps} steps a redex still remains. The term may have no normal form (e.g. Ω).",
    },
    "narrator.joke.1": {
        "pl": "Krokodyl do λ: „czemu tak się wiążesz?” λ: „bo inaczej zmiennie miałyby za dużo swobody.”",
        "en": "Crocodile to λ: \"why are you binding so much?\" λ: \"otherwise the variables would have too much freedom.\"",
    },
    "narrator.joke.2": {
        "pl": "Aligator Eggs vs. rachunek λ: to ta sama książka, tylko jajka mają zęby.",
        "en": "Alligator Eggs vs. lambda calculus: the same book — only the eggs have teeth.",
    },
    "narrator.joke.3": {
        "pl": "Jak rozpoznać λ-kalkulanta? Po tym, że mówi: „to jest *to samo* co podstawienie”.",
        "en": "How do you spot a λ-calculator? They say: \"that's *literally* substitution\".",
    },
    "narrator.vibe.var": {
        "pl": "To po prostu zmienna [brand]{name}[/brand].",
        "en": "Just a variable [brand]{name}[/brand].",
    },
    "narrator.vibe.lam": {
        "pl": "To funkcja: bierze [brand]{param}[/brand] i zwraca coś, co zależy od [brand]{param}[/brand].",
        "en": "It is a function: takes [brand]{param}[/brand] and returns something depending on [brand]{param}[/brand].",
    },
    "narrator.vibe.app": {
        "pl": "To aplikacja: funkcja zjada argument (jak krokodyl!).",
        "en": "It is an application: the function eats its argument (like a crocodile!).",
    },

    # ---- app.py Typer help strings ----
    "app.root_help": {
        "pl": "Lambda Lab — terminalowa aplikacja do wykładu „Wtyczki, kable i krokodyle”.",
        "en": "Lambda Lab — terminal companion to the lecture \"Plugs, Cables and Crocodiles\".",
    },
    "app.repl.help": {"pl": "Uruchom interaktywny REPL (domyślne).", "en": "Launch the interactive REPL (default)."},
    "app.tour.help": {"pl": "Dziesięciokrokowa wycieczka po rachunku λ.", "en": "Ten-step tour of the lambda calculus."},
    "app.reduce.help": {
        "pl": "β-redukuj podany term (z rozwinięciem stałych Churcha).",
        "en": "β-reduce a term (Church constants are expanded first).",
    },
    "app.church.help": {
        "pl": "Rozwija i dekoduje stałe Churcha. Bez argumentu pokazuje tabelkę.",
        "en": "Expand and decode Church constants. Without argument shows the table.",
    },
    "app.peano.help": {
        "pl": "Ewaluuje wyrażenie w arytmetyce Peano przez Church-numerals.",
        "en": "Evaluate an expression in Peano arithmetic via Church numerals.",
    },
    "app.alligators.help": {
        "pl": "Rysuje term jako rodziny krokodyli (ASCII).",
        "en": "Draw a term as alligator families (ASCII).",
    },
    "app.lean.help": {"pl": "Uruchamia / pokazuje dowód w Lean 4.", "en": "Run / display a Lean 4 proof."},
    "app.ag.help": {"pl": "Odtwarza dowód DD+AR z AlphaGeometry.", "en": "Replay an AlphaGeometry DD+AR proof."},
    "app.lam.help": {"pl": "Parsuje λ-term, pokazuje drzewo AST i wolne zmienne.", "en": "Parse a λ-term, show its AST and free variables."},
    "app.quiz.help": {
        "pl": "Losowe pytanie sprawdzające intuicję β-redukcji i kodowania Churcha.",
        "en": "A random question testing your intuition for β-reduction and Church encoding.",
    },
    "app.constants.help": {
        "pl": "Wyświetla tabelę wszystkich stałych Churcha (TRUE, PLUS, SUB, …). Opcjonalny argument filtruje po podciągu w nazwie, np. ``constants AND``.",
        "en": "Show the table of all Church constants (TRUE, PLUS, SUB, …). Optional argument filters by substring, e.g. ``constants AND``.",
    },
    "app.prove.help": {
        "pl": "Automatyczny dowodnik tautologii rachunkiem λ (Church + β-redukcja). Bez argumentu lub z `list` — katalog dostępnych twierdzeń.",
        "en": "Automatic tautology prover via the lambda calculus (Church + β-reduction). Without argument or with `list` — catalogue of available theorems.",
    },
    "app.prove.target": {
        "pl": "slug (np. demorgan1) albo formuła (np. 'A AND B IMPLIES A')",
        "en": "slug (e.g. demorgan1) or formula (e.g. 'A AND B IMPLIES A')",
    },
    "app.prove.trace": {
        "pl": "pokaż ślad β-redukcji dla pierwszego wartościowania",
        "en": "show the β-reduction trace for the first valuation",
    },
    "app.prove.fusion": {
        "pl": "dowód symboliczny przez Shannon expansion + IF-FUSION",
        "en": "symbolic proof via Shannon expansion + IF-FUSION",
    },
    "app.help.help": {"pl": "Wypisuje tabelkę komend.", "en": "Print the command table."},

    # ============================================================
    # Curry-Howard playground (`ch` command, 8 sub-commands)
    # ============================================================
    "cmd.ch": {
        "pl": "playground Curry-Howard: λ ↔ typ ↔ Lean ↔ taktyki",
        "en": "Curry-Howard playground: lambda calculus, types, Lean, tactics",
    },
    # ----- top-level -----
    "ch.usage": {
        "pl": "Uzycie: ch <sub> [argumenty]. Wpisz `ch` po sam panel z lista podkomend.",
        "en": "Usage: ch <sub> [args]. Type `ch` alone for the sub-command panel.",
    },
    "ch.unknown": {
        "pl": "Nieznana podkomenda `ch {sub}`. Sprobuj: term, type, lib, lean, from-lean, tactic, build, verify, explore.",
        "en": "Unknown sub-command `ch {sub}`. Try: term, type, lib, lean, from-lean, tactic, build, verify, explore.",
    },
    "ch.help.title": {"pl": "Curry-Howard playground", "en": "Curry-Howard playground"},
    "ch.help.body": {
        "pl": (
            "Most miedzy lambda-rachunkiem, typami, Lean-em i taktykami.\n\n"
            "Podkomendy:\n"
            "  ch term <lambda>         - inferuje typ + interpretacja jako dowod\n"
            "  ch type <T>              - znajduje lambda-term zamieszkujacy typ T\n"
            "  ch lib \\[name]           - katalog kombinatorow (id, K, S, B, C, Y, ...)\n"
            "  ch lean <lambda>         - generuje twierdzenie Lean 4 dla lambda\n"
            "  ch from-lean <expr>      - parsuje term Lean -> lambda + typ\n"
            "  ch tactic \\[name]        - encyklopedia 22 taktyk Lean\n"
            "  ch build <T>             - interaktywny builder dowodu (krok po kroku)\n"
            "  ch verify <theorem>      - sprawdza twierdzenie w Lean (LSP / inline)\n"
            "  ch explore \\[slug]       - interaktywny walker po katalogu twierdzen\n"
        ),
        "en": (
            "A bridge between lambda-calculus, types, Lean and tactics.\n\n"
            "Sub-commands:\n"
            "  ch term <lambda>         - infer type + proof interpretation\n"
            "  ch type <T>              - find a lambda-term inhabiting type T\n"
            "  ch lib \\[name]           - catalogue of combinators (id, K, S, B, C, Y, ...)\n"
            "  ch lean <lambda>         - generate a Lean 4 theorem for lambda\n"
            "  ch from-lean <expr>      - parse a Lean term -> lambda + type\n"
            "  ch tactic \\[name]        - encyclopedia of 22 Lean tactics\n"
            "  ch build <T>             - interactive proof builder (step by step)\n"
            "  ch verify <theorem>      - check a theorem in Lean (LSP / inline)\n"
            "  ch explore \\[slug]       - interactive walker over the theorem catalogue\n"
        ),
    },
    # ----- ch term -----
    "ch.term.usage": {
        "pl": "Uzycie: ch term <lambda>, np. `ch term \\\\p. p`.",
        "en": "Usage: ch term <lambda>, e.g. `ch term \\\\p. p`.",
    },
    "ch.term.title": {"pl": "lambda-term + typ", "en": "lambda-term + type"},
    "ch.term.row.term": {"pl": "Term", "en": "Term"},
    "ch.term.row.type": {"pl": "Typ", "en": "Type"},
    "ch.term.row.proof_of": {"pl": "Dowod tego, ze", "en": "Proof of"},
    "ch.term.row.free": {"pl": "Wolne zmienne", "en": "Free variables"},
    "ch.term.proof_interpretation": {
        "pl": "Curry-Howard: ten lambda-term jest dowodem, ze {prop}.",
        "en": "Curry-Howard: this lambda-term is a proof that {prop}.",
    },
    "ch.term.untypable": {
        "pl": "Term nietypowalny w STLC: {error}",
        "en": "Term not typeable in STLC: {error}",
    },
    "ch.term.parse_error": {
        "pl": "Nie umiem sparsowac lambda-termu: {error}",
        "en": "Cannot parse the lambda-term: {error}",
    },
    # ----- ch lean -----
    "ch.lean.usage": {
        "pl": "Uzycie: ch lean <lambda> [--name=foo]. Wygeneruje `theorem foo : T := lambda`.",
        "en": "Usage: ch lean <lambda> [--name=foo]. Produces `theorem foo : T := lambda`.",
    },
    "ch.lean.title": {"pl": "Lean 4 theorem", "en": "Lean 4 theorem"},
    "ch.lean.parse_error": {
        "pl": "Nie umiem sparsowac lambda-termu: {error}",
        "en": "Cannot parse the lambda-term: {error}",
    },
    "ch.lean.untypable": {
        "pl": "Term nietypowalny w STLC, nie da sie wystawic theorem: {error}",
        "en": "Term not typeable in STLC, cannot emit theorem: {error}",
    },
    # ----- ch lib -----
    "ch.lib.list_title": {"pl": "Katalog kombinatorow", "en": "Combinator catalogue"},
    "ch.lib.col.name": {"pl": "Nazwa", "en": "Name"},
    "ch.lib.col.aliases": {"pl": "Aliasy", "en": "Aliases"},
    "ch.lib.col.lambda": {"pl": "lambda-term", "en": "lambda-term"},
    "ch.lib.col.type": {"pl": "Typ", "en": "Type"},
    "ch.lib.col.desc": {"pl": "Co robi", "en": "What it does"},
    "ch.lib.unknown": {
        "pl": "Nieznany kombinator `{name}`. Wpisz `ch lib` po liste.",
        "en": "Unknown combinator `{name}`. Type `ch lib` to see the list.",
    },
    "ch.lib.entry_title": {"pl": "Kombinator {name}", "en": "Combinator {name}"},
    "ch.lib.row.lambda": {"pl": "lambda", "en": "lambda"},
    "ch.lib.row.type": {"pl": "Typ", "en": "Type"},
    "ch.lib.row.lean": {"pl": "Lean", "en": "Lean"},
    "ch.lib.row.aliases": {"pl": "Aliasy", "en": "Aliases"},
    "ch.lib.row.untypeable": {"pl": "(nietypowalny w STLC)", "en": "(not typeable in STLC)"},
    "ch.lib.entry.id": {
        "pl": "Identycznosc - oddaje argument bez zmian; logicznie: `P -> P`.",
        "en": "Identity - returns its argument unchanged; logically: `P -> P`.",
    },
    "ch.lib.entry.K": {
        "pl": "Stala - bierze dwa argumenty, zwraca pierwszy; logicznie: `P -> Q -> P`.",
        "en": "Constant - takes two arguments, returns the first; logically: `P -> Q -> P`.",
    },
    "ch.lib.entry.S": {
        "pl": "Substytutor - rozdziela argument do f i g; logicznie axiom S Hilberta.",
        "en": "Substitutor - distributes the argument to f and g; logically Hilbert's S.",
    },
    "ch.lib.entry.B": {
        "pl": "Komponowanie - klasyczne f . g; logicznie tranzytywnosc implikacji.",
        "en": "Composition - the classic f . g; logically transitivity of implication.",
    },
    "ch.lib.entry.C": {
        "pl": "Flip - zamienia kolejnosc dwoch argumentow.",
        "en": "Flip - swaps the order of two arguments.",
    },
    "ch.lib.entry.Y": {
        "pl": "Punkt staly - rekursja w bezhipotetycznym lambdzie; nietypowalny w STLC.",
        "en": "Fixed point - recursion in unhypothesised lambda; untypeable in STLC.",
    },
    "ch.lib.entry.fst": {
        "pl": "Pierwsza projekcja - alias K (dla pary curried).",
        "en": "First projection - alias of K (for a curried pair).",
    },
    "ch.lib.entry.snd": {
        "pl": "Druga projekcja - K I; bierze dwa, zwraca drugi.",
        "en": "Second projection - K I; takes two, returns the second.",
    },
    "ch.lib.entry.app": {
        "pl": "Aplikacja - explicytnie `\\f x. f x`; eta-expansja identycznosci.",
        "en": "Application - explicitly `\\f x. f x`; eta-expansion of identity.",
    },
    "ch.lib.entry.const": {
        "pl": "Synonim K.",
        "en": "Synonym for K.",
    },
    "ch.lib.entry.W": {
        "pl": "Duplikator - `\\f x. f x x`; podaje `x` dwukrotnie do `f`.",
        "en": "Duplicator - `\\f x. f x x`; feeds `x` to `f` twice.",
    },
    "ch.lib.entry.O": {
        "pl": "Sowa - `\\f g. g (f g)`; nietypowalny w STLC bez polimorfizmu.",
        "en": "Owl - `\\f g. g (f g)`; not typeable in STLC without polymorphism.",
    },

    # ----- ch type (proof search) -----
    "ch.type.usage": {
        "pl": "Uzycie: ch type <T>, np. `ch type 'P -> P'`. Wyszukuje lambda-term zamieszkujacy T.",
        "en": "Usage: ch type <T>, e.g. `ch type 'P -> P'`. Finds a lambda-term inhabiting T.",
    },
    "ch.type.title": {"pl": "Wyszukany dowod", "en": "Found proof"},
    "ch.type.row.type": {"pl": "Cel", "en": "Goal"},
    "ch.type.row.term": {"pl": "Lambda-term", "en": "Lambda-term"},
    "ch.type.row.lean": {"pl": "Lean", "en": "Lean"},
    "ch.type.parse_error": {
        "pl": "Nie umiem sparsowac typu: {error}",
        "en": "Cannot parse type: {error}",
    },
    "ch.type.not_inhabited": {
        "pl": "Typ {type} nie jest zamieszkany w intuicjonistycznym STLC (klasyczne dowody jak Peirce nie maja konstruktywnego swiadka).",
        "en": "Type {type} is not inhabited in intuitionistic STLC (classical theorems like Peirce have no constructive witness).",
    },
    "ch.type.search_depth": {"pl": "Glebokosc szukania: {depth}", "en": "Search depth: {depth}"},

    # ----- ch from-lean -----
    "ch.from_lean.usage": {
        "pl": "Uzycie: ch from-lean '<expr>', np. `ch from-lean 'fun p => p'`.",
        "en": "Usage: ch from-lean '<expr>', e.g. `ch from-lean 'fun p => p'`.",
    },
    "ch.from_lean.title": {"pl": "Lean -> lambda", "en": "Lean -> lambda"},
    "ch.from_lean.row.lean": {"pl": "Lean", "en": "Lean"},
    "ch.from_lean.row.lambda": {"pl": "Lambda-term", "en": "Lambda-term"},
    "ch.from_lean.row.type": {"pl": "Typ", "en": "Type"},
    "ch.from_lean.parse_error": {
        "pl": "Nie umiem sparsowac wyrazenia Lean: {error}",
        "en": "Cannot parse Lean expression: {error}",
    },
    "ch.from_lean.untypable": {
        "pl": "Sparsowano, ale typ nie istnieje w STLC: {error}",
        "en": "Parsed, but type does not exist in STLC: {error}",
    },

    # ----- ch tactic -----
    "ch.tactic.usage": {
        "pl": "Uzycie: ch tactic [name]. Bez argumentu wypisuje katalog 22 taktyk.",
        "en": "Usage: ch tactic [name]. Without argument prints the catalogue of 22 tactics.",
    },
    "ch.tactic.list_title": {
        "pl": "Encyklopedia 22 taktyk Lean 4",
        "en": "Encyclopedia of 22 Lean 4 tactics",
    },
    "ch.tactic.col.name": {"pl": "Taktyka", "en": "Tactic"},
    "ch.tactic.col.summary": {"pl": "Krotki opis", "en": "Short description"},
    "ch.tactic.unknown": {
        "pl": "Nieznana taktyka `{name}`. Sprawdz `ch tactic` aby zobaczyc liste.",
        "en": "Unknown tactic `{name}`. Run `ch tactic` to see the list.",
    },
    "ch.tactic.entry_title": {
        "pl": "Taktyka {name}",
        "en": "Tactic {name}",
    },
    "ch.tactic.row.summary": {"pl": "Krotko", "en": "Summary"},
    "ch.tactic.row.lambda": {"pl": "Na lambda-termie", "en": "On the lambda-term"},
    "ch.tactic.row.goal": {"pl": "Na celu", "en": "On the goal"},
    "ch.tactic.row.when": {"pl": "Kiedy stosowac", "en": "When to apply"},
    "ch.tactic.row.example_goal": {"pl": "Przyklad - cel", "en": "Example - goal"},
    "ch.tactic.row.example_after": {"pl": "Po taktyce", "en": "After the tactic"},

    # ----- ch tactic encyklopedia: 22 taktyk x 4 klucze = 88 -----

    # intro
    "ch.tactic.intro.summary": {
        "pl": "Wprowadza zalozenie implikacji jako nazwana hipoteze.",
        "en": "Introduces the assumption of an implication as a named hypothesis.",
    },
    "ch.tactic.intro.lambda_effect": {
        "pl": "Dodaje wokol celu nowy lambda-binder (np. `fun p => ?`).",
        "en": "Wraps the goal in a new lambda-binder (e.g. `fun p => ?`).",
    },
    "ch.tactic.intro.goal_effect": {
        "pl": "Zamienia cel `A -> B` w cel `B` z `x : A` w kontekscie.",
        "en": "Turns goal `A -> B` into `B` with `x : A` in the context.",
    },
    "ch.tactic.intro.when": {
        "pl": "Gdy cel jest implikacja albo funkcja typu zaleznego.",
        "en": "When the goal is an implication or a Pi-type.",
    },

    # intros
    "ch.tactic.intros.summary": {
        "pl": "Wprowadza naraz wszystkie zalozenia z lancucha implikacji.",
        "en": "Introduces all hypotheses from a chain of implications at once.",
    },
    "ch.tactic.intros.lambda_effect": {
        "pl": "Dokleja kilka lambda-binderow `fun p q r => ?` na raz.",
        "en": "Adds several lambda-binders `fun p q r => ?` in one step.",
    },
    "ch.tactic.intros.goal_effect": {
        "pl": "Zamienia `A -> B -> C` w cel `C` z `A`, `B` w kontekscie.",
        "en": "Turns `A -> B -> C` into goal `C` with `A`, `B` in the context.",
    },
    "ch.tactic.intros.when": {
        "pl": "Gdy cel ma kilka implikacji lub kwantyfikatorow z rzedu.",
        "en": "When the goal has several stacked implications or quantifiers.",
    },

    # exact
    "ch.tactic.exact.summary": {
        "pl": "Zamyka cel podajac dokladny term tego samego typu.",
        "en": "Closes the goal by providing an exact term of the same type.",
    },
    "ch.tactic.exact.lambda_effect": {
        "pl": "Wstawia podany term w miejsce dziury `?` w czesciowym dowodzie.",
        "en": "Plugs the given term into the hole `?` of the partial proof.",
    },
    "ch.tactic.exact.goal_effect": {
        "pl": "Cel znika z listy, jezeli typy sie zgadzaja.",
        "en": "The goal disappears from the list when the types match.",
    },
    "ch.tactic.exact.when": {
        "pl": "Gdy juz wiesz, jaki term jest dowodem (np. masz hipoteze).",
        "en": "When you already know the term that proves the goal.",
    },

    # apply
    "ch.tactic.apply.summary": {
        "pl": "Stosuje funkcje (implikacje), redukujac cel do jej argumentow.",
        "en": "Applies a function (implication), reducing the goal to its arguments.",
    },
    "ch.tactic.apply.lambda_effect": {
        "pl": "Tworzy aplikacje `f ?` i zostawia dziury na argumenty `f`.",
        "en": "Builds an application `f ?` and leaves holes for the arguments of `f`.",
    },
    "ch.tactic.apply.goal_effect": {
        "pl": "Zamiast `Q` celem staje sie `P`, jezeli `f : P -> Q`.",
        "en": "Instead of `Q` the goal becomes `P`, when `f : P -> Q`.",
    },
    "ch.tactic.apply.when": {
        "pl": "Gdy znasz funkcje, ktorej kodziedzina pasuje do celu.",
        "en": "When you know a function whose codomain matches the goal.",
    },

    # refine
    "ch.tactic.refine.summary": {
        "pl": "Wstawia term z dziurami `?_` i tworzy podcele dla kazdej dziury.",
        "en": "Plugs in a term with holes `?_` and opens a subgoal for each hole.",
    },
    "ch.tactic.refine.lambda_effect": {
        "pl": "Czesciowy term zostaje wzbogacony o szkielet, dziury zostaja.",
        "en": "Enriches the partial term with a skeleton; holes remain to fill.",
    },
    "ch.tactic.refine.goal_effect": {
        "pl": "Jeden cel rozbija sie na tyle podcelow, ile jest `?_`.",
        "en": "One goal splits into as many subgoals as there are `?_` holes.",
    },
    "ch.tactic.refine.when": {
        "pl": "Gdy znasz strukture dowodu, ale czesc szczegolow chcesz odlozyc.",
        "en": "When you know the proof shape but want to defer some details.",
    },

    # rfl
    "ch.tactic.rfl.summary": {
        "pl": "Zamyka cel rownosci `a = a` przez refleksywnosc.",
        "en": "Closes an equality goal `a = a` by reflexivity.",
    },
    "ch.tactic.rfl.lambda_effect": {
        "pl": "Wstawia kanoniczny dowod `Eq.refl a` w miejsce dziury.",
        "en": "Inserts the canonical proof `Eq.refl a` into the hole.",
    },
    "ch.tactic.rfl.goal_effect": {
        "pl": "Cel `a = a` znika; nic wiecej do zrobienia.",
        "en": "Goal `a = a` disappears; nothing more to do.",
    },
    "ch.tactic.rfl.when": {
        "pl": "Gdy obie strony rownosci sa definicyjnie identyczne.",
        "en": "When both sides of the equality are definitionally identical.",
    },

    # cases
    "ch.tactic.cases.summary": {
        "pl": "Rozbija hipoteze na przypadki (np. lewy/prawy dla alternatywy).",
        "en": "Splits a hypothesis into cases (e.g. left/right for a disjunction).",
    },
    "ch.tactic.cases.lambda_effect": {
        "pl": "Buduje `match` lub kilka galezi w czesciowym termie.",
        "en": "Builds a `match` or several branches in the partial term.",
    },
    "ch.tactic.cases.goal_effect": {
        "pl": "Jeden cel staje sie kilkoma podcelami, po jednym na konstruktor.",
        "en": "One goal becomes several subgoals, one per constructor.",
    },
    "ch.tactic.cases.when": {
        "pl": "Gdy hipoteza jest typu indukcyjnego (`Or`, `Nat`, `Sum`, ...).",
        "en": "When a hypothesis has an inductive type (`Or`, `Nat`, `Sum`, ...).",
    },

    # rcases
    "ch.tactic.rcases.summary": {
        "pl": "Wzbogacone `cases` z wzorcami: rozbija i nazywa od razu.",
        "en": "Enhanced `cases` with patterns: splits and names in one step.",
    },
    "ch.tactic.rcases.lambda_effect": {
        "pl": "Tworzy zagniezdzony `match` z nazwanymi wiazaniami.",
        "en": "Builds a nested `match` with named bindings.",
    },
    "ch.tactic.rcases.goal_effect": {
        "pl": "Hipoteza koniunkcji `A and B` daje natychmiast `ha`, `hb`.",
        "en": "A conjunction `A and B` yields `ha`, `hb` immediately.",
    },
    "ch.tactic.rcases.when": {
        "pl": "Gdy chcesz w jednym kroku zlozyc kilka rozbic i nazwac czesci.",
        "en": "When you want to combine several splits and name the parts at once.",
    },

    # induction
    "ch.tactic.induction.summary": {
        "pl": "Indukcja po typie indukcyjnym (np. po `Nat` z baza i krokiem).",
        "en": "Induction over an inductive type (e.g. on `Nat` with base and step).",
    },
    "ch.tactic.induction.lambda_effect": {
        "pl": "Buduje rekursor `Nat.rec` (lub odpowiednik) jako szkielet termu.",
        "en": "Builds a recursor `Nat.rec` (or analogue) as the term skeleton.",
    },
    "ch.tactic.induction.goal_effect": {
        "pl": "Cel `P n` rozpada sie na `P 0` oraz `P n -> P (n+1)`.",
        "en": "Goal `P n` splits into `P 0` and `P n -> P (n+1)`.",
    },
    "ch.tactic.induction.when": {
        "pl": "Gdy musisz dowiesc wlasnosci dla wszystkich elementow typu indukcyjnego.",
        "en": "When you must prove a property for all elements of an inductive type.",
    },

    # by_contra
    "ch.tactic.by_contra.summary": {
        "pl": "Dowod nie wprost: zaklada `not P` i prowadzi do sprzecznosci.",
        "en": "Proof by contradiction: assume `not P` and derive a contradiction.",
    },
    "ch.tactic.by_contra.lambda_effect": {
        "pl": "Wprowadza `Classical.byContradiction` i nowa hipoteze `h : not P`.",
        "en": "Introduces `Classical.byContradiction` and a new hypothesis `h : not P`.",
    },
    "ch.tactic.by_contra.goal_effect": {
        "pl": "Zamiast `P` celem staje sie `False` z `h : not P` w kontekscie.",
        "en": "Instead of `P` the goal becomes `False` with `h : not P` in context.",
    },
    "ch.tactic.by_contra.when": {
        "pl": "Gdy bezposrednia konstrukcja zawodzi i potrzebujesz logiki klasycznej.",
        "en": "When direct construction fails and you need classical logic.",
    },

    # contradiction
    "ch.tactic.contradiction.summary": {
        "pl": "Zamyka cel, gdy w kontekscie sa hipotezy `h : P` oraz `not h : not P`.",
        "en": "Closes the goal when the context has both `h : P` and `not h : not P`.",
    },
    "ch.tactic.contradiction.lambda_effect": {
        "pl": "Wstawia `absurd h not_h` jako kompletny term.",
        "en": "Inserts `absurd h not_h` as a complete term.",
    },
    "ch.tactic.contradiction.goal_effect": {
        "pl": "Dowolny cel znika - z falszu wynika wszystko.",
        "en": "Any goal disappears - ex falso sequitur quodlibet.",
    },
    "ch.tactic.contradiction.when": {
        "pl": "Gdy w hipotezach widzisz parke `P` i `not P` (lub `False`).",
        "en": "When you see a pair `P` and `not P` (or `False`) in the hypotheses.",
    },

    # tauto
    "ch.tactic.tauto.summary": {
        "pl": "Decyduje tautologie logiki klasycznej zdaniowej.",
        "en": "Decides classical propositional tautologies.",
    },
    "ch.tactic.tauto.lambda_effect": {
        "pl": "Buduje term automatycznie - nie widac go bezposrednio.",
        "en": "Builds the term automatically - it is not shown directly.",
    },
    "ch.tactic.tauto.goal_effect": {
        "pl": "Cel zostaje zamkniety (lub taktyka pada z bledem).",
        "en": "The goal is closed (or the tactic fails outright).",
    },
    "ch.tactic.tauto.when": {
        "pl": "Gdy cel jest tautologia zlozona z `and`, `or`, `not`, `->`, `<->`.",
        "en": "When the goal is a tautology built from `and`, `or`, `not`, `->`, `<->`.",
    },

    # simp
    "ch.tactic.simp.summary": {
        "pl": "Upraszcza cel, stosujac lematy oznaczone `@[simp]`.",
        "en": "Simplifies the goal by applying lemmas tagged `@[simp]`.",
    },
    "ch.tactic.simp.lambda_effect": {
        "pl": "Wstawia ciag przepisan; finalny term jest zlozony przez `simp`.",
        "en": "Inserts a chain of rewrites; the final term is assembled by `simp`.",
    },
    "ch.tactic.simp.goal_effect": {
        "pl": "Cel staje sie kanoniczna forma; czesto sam sie zamyka.",
        "en": "The goal becomes canonical form; often closes by itself.",
    },
    "ch.tactic.simp.when": {
        "pl": "Gdy cel mozna sprowadzic do prawdy przez znane przepisania.",
        "en": "When the goal can be reduced to truth by known rewrites.",
    },

    # rw
    "ch.tactic.rw.summary": {
        "pl": "Przepisuje wystapienia uzywajac rownosci `h : a = b`.",
        "en": "Rewrites occurrences using an equality `h : a = b`.",
    },
    "ch.tactic.rw.lambda_effect": {
        "pl": "Wstawia `Eq.mpr` lub `Eq.subst` do czesciowego termu.",
        "en": "Inserts `Eq.mpr` or `Eq.subst` into the partial term.",
    },
    "ch.tactic.rw.goal_effect": {
        "pl": "W celu kazde `a` zamienia sie w `b` (lub odwrotnie z `<-`).",
        "en": "In the goal each `a` becomes `b` (or vice versa with `<-`).",
    },
    "ch.tactic.rw.when": {
        "pl": "Gdy masz rownosc i chcesz zaaplikowac ja do celu lub hipotezy.",
        "en": "When you have an equality and want to apply it to a goal or hypothesis.",
    },

    # calc
    "ch.tactic.calc.summary": {
        "pl": "Lancuchowy dowod krok-po-kroku, np. `a = b = c < d`.",
        "en": "Step-by-step chained proof, e.g. `a = b = c < d`.",
    },
    "ch.tactic.calc.lambda_effect": {
        "pl": "Buduje term `Trans.trans` lub `Eq.trans` z kolejnych ogniw.",
        "en": "Builds a term using `Trans.trans` or `Eq.trans` for each link.",
    },
    "ch.tactic.calc.goal_effect": {
        "pl": "Cel zostaje rozlozony na kolejne male kroki nierownosci/rownosci.",
        "en": "The goal decomposes into consecutive small inequality/equality steps.",
    },
    "ch.tactic.calc.when": {
        "pl": "Gdy lancuchujesz nierownosci albo wieloetapowe rownosci.",
        "en": "When you chain inequalities or multi-step equalities.",
    },

    # use
    "ch.tactic.use.summary": {
        "pl": "Podaje swiadka dla celu egzystencjalnego `exists x, P x`.",
        "en": "Supplies a witness for an existential goal `exists x, P x`.",
    },
    "ch.tactic.use.lambda_effect": {
        "pl": "Tworzy parke `<witness, ?>` i zostawia dziure na dowod `P witness`.",
        "en": "Builds a pair `<witness, ?>` leaving a hole for the proof of `P witness`.",
    },
    "ch.tactic.use.goal_effect": {
        "pl": "Cel `exists x, P x` zamienia sie w `P witness`.",
        "en": "Goal `exists x, P x` turns into `P witness`.",
    },
    "ch.tactic.use.when": {
        "pl": "Gdy cel jest egzystencjalny i znasz konkretnego swiadka.",
        "en": "When the goal is existential and you know a concrete witness.",
    },

    # constructor
    "ch.tactic.constructor.summary": {
        "pl": "Wybiera pierwszy konstruktor typu indukcyjnego (np. `And.intro`).",
        "en": "Picks the first constructor of an inductive type (e.g. `And.intro`).",
    },
    "ch.tactic.constructor.lambda_effect": {
        "pl": "Wstawia `Foo.mk ?a ?b` z dziurami na pola.",
        "en": "Inserts `Foo.mk ?a ?b` with holes for the fields.",
    },
    "ch.tactic.constructor.goal_effect": {
        "pl": "Cel `A and B` rozbija sie na `A` i `B`.",
        "en": "Goal `A and B` splits into `A` and `B`.",
    },
    "ch.tactic.constructor.when": {
        "pl": "Gdy cel jest typu z jednym sensownym konstruktorem (`And`, `Iff`, ...).",
        "en": "When the goal type has one canonical constructor (`And`, `Iff`, ...).",
    },

    # left
    "ch.tactic.left.summary": {
        "pl": "Wybiera lewa galaz alternatywy `A or B`.",
        "en": "Chooses the left branch of a disjunction `A or B`.",
    },
    "ch.tactic.left.lambda_effect": {
        "pl": "Wstawia `Or.inl ?` w miejsce dziury.",
        "en": "Inserts `Or.inl ?` at the hole.",
    },
    "ch.tactic.left.goal_effect": {
        "pl": "Cel `A or B` upraszcza sie do `A`.",
        "en": "Goal `A or B` simplifies to `A`.",
    },
    "ch.tactic.left.when": {
        "pl": "Gdy chcesz dowiesc lewej strony alternatywy.",
        "en": "When you want to prove the left side of the disjunction.",
    },

    # right
    "ch.tactic.right.summary": {
        "pl": "Wybiera prawa galaz alternatywy `A or B`.",
        "en": "Chooses the right branch of a disjunction `A or B`.",
    },
    "ch.tactic.right.lambda_effect": {
        "pl": "Wstawia `Or.inr ?` w miejsce dziury.",
        "en": "Inserts `Or.inr ?` at the hole.",
    },
    "ch.tactic.right.goal_effect": {
        "pl": "Cel `A or B` upraszcza sie do `B`.",
        "en": "Goal `A or B` simplifies to `B`.",
    },
    "ch.tactic.right.when": {
        "pl": "Gdy chcesz dowiesc prawej strony alternatywy.",
        "en": "When you want to prove the right side of the disjunction.",
    },

    # exists
    "ch.tactic.exists.summary": {
        "pl": "Skrocony zapis `use` dla egzystencjalnych celow.",
        "en": "Shorthand for `use` on existential goals.",
    },
    "ch.tactic.exists.lambda_effect": {
        "pl": "Wstawia konstruktor `Exists.intro witness ?` w czesciowym termie.",
        "en": "Inserts the constructor `Exists.intro witness ?` into the partial term.",
    },
    "ch.tactic.exists.goal_effect": {
        "pl": "Cel `exists x, P x` redukuje sie do `P witness`.",
        "en": "Goal `exists x, P x` reduces to `P witness`.",
    },
    "ch.tactic.exists.when": {
        "pl": "Gdy znasz swiadka i wolisz krotka skladnie zamiast `use`.",
        "en": "When you have a witness and prefer the short syntax over `use`.",
    },

    # assumption
    "ch.tactic.assumption.summary": {
        "pl": "Szuka w kontekscie hipotezy o typie celu i ja stosuje.",
        "en": "Searches the context for a hypothesis matching the goal and uses it.",
    },
    "ch.tactic.assumption.lambda_effect": {
        "pl": "Wstawia nazwe pasujacej hipotezy w miejsce dziury.",
        "en": "Plugs the name of the matching hypothesis into the hole.",
    },
    "ch.tactic.assumption.goal_effect": {
        "pl": "Cel znika, jesli pasujaca hipoteza zostala znaleziona.",
        "en": "The goal disappears if a matching hypothesis was found.",
    },
    "ch.tactic.assumption.when": {
        "pl": "Gdy cel slowo w slowo wystepuje juz w kontekscie.",
        "en": "When the goal already appears verbatim in the context.",
    },

    # decide
    "ch.tactic.decide.summary": {
        "pl": "Decyduje cel rozstrzygalny przez obliczenie (np. `2 + 2 = 4`).",
        "en": "Decides a decidable goal by computation (e.g. `2 + 2 = 4`).",
    },
    "ch.tactic.decide.lambda_effect": {
        "pl": "Wstawia `Decidable.decide` z dowodem przez reflekcje.",
        "en": "Inserts `Decidable.decide` with a proof by reflection.",
    },
    "ch.tactic.decide.goal_effect": {
        "pl": "Cel zamyka sie obliczeniowo lub taktyka pada.",
        "en": "The goal closes by computation or the tactic fails.",
    },
    "ch.tactic.decide.when": {
        "pl": "Gdy cel jest typu `Decidable` (rownosc liczb, predykat boolowski).",
        "en": "When the goal has type `Decidable` (number equality, boolean predicate).",
    },
    # ----- newly added tactics: omega, ring, linarith, norm_num, trivial -----
    "ch.tactic.omega.summary":       {"pl": "Procedura decyzyjna dla arytmetyki Presburgera (Nat/Int).",
                                      "en": "Decision procedure for Presburger arithmetic (Nat/Int)."},
    "ch.tactic.omega.lambda_effect": {"pl": "Wstawia certyfikat liniowy lub pada.",
                                      "en": "Inserts a linear-arithmetic certificate or fails."},
    "ch.tactic.omega.goal_effect":   {"pl": "Cel zamyka sie jezeli da sie sprowadzic do (in)rownosci liniowych.",
                                      "en": "Closes the goal if it reduces to linear (in)equalities."},
    "ch.tactic.omega.when":          {"pl": "Liniowe rownosci/nierownosci nad Nat/Int (a + b = b + a, n ≤ n + 1).",
                                      "en": "Linear (in)equalities over Nat/Int (a + b = b + a, n ≤ n + 1)."},
    "ch.tactic.ring.summary":       {"pl": "Normalizuje wyrazenia w pierscieniu przemiennym (rownosc).",
                                     "en": "Normalises expressions in a commutative (semi)ring (equality)."},
    "ch.tactic.ring.lambda_effect": {"pl": "Wstawia dowod rownosci po sprowadzeniu do postaci kanonicznej.",
                                     "en": "Inserts an equality proof after reducing to canonical form."},
    "ch.tactic.ring.goal_effect":   {"pl": "Zamyka rownosc gdy obie strony rowne w jezyku ringu.",
                                     "en": "Closes the equality when both sides are equal in the ring language."},
    "ch.tactic.ring.when":          {"pl": "Wielomianowe tozsamosci: (a+b)^2 = a^2 + 2ab + b^2.",
                                     "en": "Polynomial identities: (a+b)^2 = a^2 + 2ab + b^2."},
    "ch.tactic.linarith.summary":       {"pl": "Liniowa arytmetyka nad uporzadkowanym cialem (≤, <, =).",
                                         "en": "Linear arithmetic over an ordered field (≤, <, =)."},
    "ch.tactic.linarith.lambda_effect": {"pl": "Buduje kombinacje liniowa hipotez zamykajaca cel.",
                                         "en": "Builds a linear combination of hypotheses that closes the goal."},
    "ch.tactic.linarith.goal_effect":   {"pl": "Cel domyka sie jezeli wynika liniowo z dostepnych hipotez.",
                                         "en": "The goal closes if it follows linearly from the hypotheses."},
    "ch.tactic.linarith.when":          {"pl": "Przechodnie nierownosci, sumy/odejmowania w hipotezach.",
                                         "en": "Transitive inequalities, sums/subtractions among hypotheses."},
    "ch.tactic.norm_num.summary":       {"pl": "Upraszcza wyrazenia numeryczne (mnozenie, dzielenie, potegowanie).",
                                         "en": "Normalises numeric expressions (multiplication, division, powers)."},
    "ch.tactic.norm_num.lambda_effect": {"pl": "Zastepuje cel jego znormalizowana liczbowo postacia.",
                                         "en": "Replaces the goal with its numerically-normalised form."},
    "ch.tactic.norm_num.goal_effect":   {"pl": "Cel zamyka sie po obliczeniu literalow.",
                                         "en": "The goal closes after computing the literal values."},
    "ch.tactic.norm_num.when":          {"pl": "Konkretne liczby: 2 + 3 * 4 = 14, sqrt 9 = 3.",
                                         "en": "Concrete numbers: 2 + 3 * 4 = 14, sqrt 9 = 3."},
    "ch.tactic.trivial.summary":       {"pl": "Probuje rfl, assumption, decide — uniwersalna pierwsza proba.",
                                        "en": "Tries rfl, assumption, decide — universal first attempt."},
    "ch.tactic.trivial.lambda_effect": {"pl": "Wstawia term jezeli ktoras prosta taktyka zadziala.",
                                        "en": "Inserts a term if any of the simple tactics succeeds."},
    "ch.tactic.trivial.goal_effect":   {"pl": "Cel zamyka sie albo taktyka pada (bez postepu).",
                                        "en": "The goal closes or the tactic fails (no progress)."},
    "ch.tactic.trivial.when":          {"pl": "Gdy cel jest oczywisty: True, x = x, hipoteza w kontekscie.",
                                        "en": "When the goal is obvious: True, x = x, a hypothesis in context."},
    # ----- Mathlib lemma summaries (referenced in `available_tactics` as dotted names) -----
    "ch.tactic.lemma.Nat_zero_add.summary":  {"pl": "0 + n = n", "en": "0 + n = n"},
    "ch.tactic.lemma.Nat_add_zero.summary":  {"pl": "n + 0 = n", "en": "n + 0 = n"},
    "ch.tactic.lemma.Nat_add_comm.summary":  {"pl": "a + b = b + a", "en": "a + b = b + a"},
    "ch.tactic.lemma.Nat_add_assoc.summary": {"pl": "(a + b) + c = a + (b + c)", "en": "(a + b) + c = a + (b + c)"},
    "ch.tactic.lemma.Nat_zero_mul.summary":  {"pl": "0 * n = 0", "en": "0 * n = 0"},
    "ch.tactic.lemma.Nat_one_mul.summary":   {"pl": "1 * n = n", "en": "1 * n = n"},
    "ch.tactic.lemma.Nat_mul_add.summary":   {"pl": "a * (b + c) = a * b + a * c", "en": "a * (b + c) = a * b + a * c"},
    "ch.tactic.lemma.Nat_mul_assoc.summary": {"pl": "(a * b) * c = a * (b * c)", "en": "(a * b) * c = a * (b * c)"},

    # ----- ch build -----
    "ch.build.usage": {
        "pl": "Uzycie: ch build <typ>, np. `ch build P -> P`.",
        "en": "Usage: ch build <type>, e.g. `ch build P -> P`.",
    },
    "ch.build.title": {"pl": "Builder dowodu", "en": "Proof builder"},
    "ch.build.goal_label": {"pl": "Cel {idx}/{total}", "en": "Goal {idx}/{total}"},
    "ch.build.context_label": {"pl": "Kontekst", "en": "Context"},
    "ch.build.target_label": {"pl": "Tez", "en": "Target"},
    "ch.build.term_label": {"pl": "Term", "en": "Term"},
    "ch.build.empty_context": {"pl": "(pusty)", "en": "(empty)"},
    "ch.build.tactics_hint": {
        "pl": "Taktyki: intro [name], exact <term>, apply <term>, assumption, refine <term>, hint, undo, done, quit. Wpisz `t` po sciaga.",
        "en": "Tactics: intro [name], exact <term>, apply <term>, assumption, refine <term>, hint, undo, done, quit. Type `t` for a cheat sheet.",
    },
    "ch.build.tactics_ref.title": {
        "pl": "Sciaga: skladnia taktyk buildera",
        "en": "Cheat sheet: builder tactic syntax",
    },
    "ch.build.tactics_ref.meta.hint":    {"pl": "Sugeruje nastepny krok (proof search).",  "en": "Suggests the next step (proof search)."},
    "ch.build.tactics_ref.meta.undo":    {"pl": "Cofnij ostatnia taktyke.",                "en": "Undo the last tactic."},
    "ch.build.tactics_ref.meta.done":    {"pl": "Zakoncz (gdy wszystkie cele zamkniete).", "en": "Finish (when all goals are closed)."},
    "ch.build.tactics_ref.meta.quit":    {"pl": "Wyjdz z buildera.",                       "en": "Leave the builder."},
    "ch.build.tactics_ref.meta.show":    {"pl": "Pokaz aktualny stan dowodu.",             "en": "Show the current proof state."},
    "ch.build.tactics_ref.meta.tactics": {"pl": "Pokaz te sciage.",                        "en": "Show this cheat sheet."},
    "ch.build.prompt": {"pl": "[ch.build]> ", "en": "[ch.build]> "},
    "ch.build.unknown_tactic": {
        "pl": "Nieznana taktyka `{name}`. Wpisz `hint` po podpowiedz lub `quit` po wyjscie.",
        "en": "Unknown tactic `{name}`. Type `hint` for a suggestion or `quit` to exit.",
    },
    "ch.build.no_more_goals": {
        "pl": "Wszystkie cele zamkniete.",
        "en": "All goals closed.",
    },
    "ch.build.undo_done": {
        "pl": "Cofnieto ostatni krok.",
        "en": "Last step undone.",
    },
    "ch.build.history_empty": {
        "pl": "Historia jest pusta - nic do cofniecia.",
        "en": "History is empty - nothing to undo.",
    },
    "ch.build.tactic_error": {
        "pl": "Blad taktyki: {error}",
        "en": "Tactic error: {error}",
    },
    "ch.build.parse_error": {
        "pl": "Nie umiem sparsowac typu: {error}",
        "en": "Cannot parse type: {error}",
    },
    "ch.build.final_term": {
        "pl": "Koncowy lambda-term",
        "en": "Final lambda-term",
    },
    "ch.build.lean_theorem": {
        "pl": "Twierdzenie Lean",
        "en": "Lean theorem",
    },
    "ch.build.hint_suggest": {
        "pl": "Podpowiedz: sprobuj `exact {term}`.",
        "en": "Hint: try `exact {term}`.",
    },
    "ch.build.hint_none": {
        "pl": "Brak automatycznej podpowiedzi dla biezacego celu.",
        "en": "No automatic hint for the current goal.",
    },
    "ch.build.bye": {"pl": "Wychodze z builder-a.", "en": "Leaving the builder."},
    "ch.build.goal_not_implication": {
        "pl": "Cel `{target}` nie jest implikacja - `intro` tu nie zadziala.",
        "en": "Goal `{target}` is not an implication - `intro` does not apply here.",
    },
    "ch.build.exact_needs_arg": {
        "pl": "Taktyka `exact` potrzebuje argumentu, np. `exact p`.",
        "en": "Tactic `exact` needs an argument, e.g. `exact p`.",
    },
    "ch.build.apply_needs_arg": {
        "pl": "Taktyka `apply` potrzebuje argumentu (funkcji do zaaplikowania).",
        "en": "Tactic `apply` needs an argument (the function to apply).",
    },
    "ch.build.refine_needs_arg": {
        "pl": "Taktyka `refine` potrzebuje termu z dziurami `?_`.",
        "en": "Tactic `refine` needs a term with holes `?_`.",
    },
    "ch.build.exact_type_mismatch": {
        "pl": "Term `{term}` ma typ `{got}`, a cel to `{want}`.",
        "en": "Term `{term}` has type `{got}` but the goal is `{want}`.",
    },
    "ch.build.apply_not_implication": {
        "pl": "`{term}` nie jest funkcja - `apply` wymaga implikacji.",
        "en": "`{term}` is not a function - `apply` needs an implication.",
    },
    "ch.build.unknown_term": {
        "pl": "Nie znam termu `{term}` w biezacym kontekscie.",
        "en": "I do not know term `{term}` in the current context.",
    },
    "ch.build.assumption_no_match": {
        "pl": "Zadna hipoteza nie pasuje do celu `{target}`.",
        "en": "No hypothesis matches the goal `{target}`.",
    },
    "ch.build.done_without_close": {
        "pl": "Sa jeszcze otwarte cele - nie mozna zakonczyc.",
        "en": "There are still open goals - cannot finish.",
    },

    # ----- ch verify -----
    "ch.verify.usage": {
        "pl": "Uzycie: ch verify <theorem-string> [--backend server|inline|auto].",
        "en": "Usage: ch verify <theorem-string> [--backend server|inline|auto].",
    },
    "ch.verify.title": {"pl": "Weryfikacja Lean", "en": "Lean verification"},
    "ch.verify.ok": {
        "pl": "Twierdzenie poprawne ({backend}, {elapsed:.2f}s).",
        "en": "Theorem checks ({backend}, {elapsed:.2f}s).",
    },
    "ch.verify.fail": {
        "pl": "Lean odrzucil dowod ({backend}, {elapsed:.2f}s, bledy: {errors}).",
        "en": "Lean rejected the proof ({backend}, {elapsed:.2f}s, errors: {errors}).",
    },
    "ch.verify.backend_used": {
        "pl": "Backend: {backend}",
        "en": "Backend: {backend}",
    },
    "ch.verify.no_lake": {
        "pl": "Brak projektu Lake w `{path}` - weryfikacja niedostepna.",
        "en": "No Lake project at `{path}` - verification unavailable.",
    },
    "ch.verify.lake_missing": {
        "pl": "Polecenie `lake` nie zostalo znalezione - zainstaluj elan/lake.",
        "en": "`lake` command not found - install elan/lake first.",
    },
    "ch.verify.timeout": {
        "pl": "Lean nie odpowiedzial w czasie {timeout}s.",
        "en": "Lean did not respond within {timeout}s.",
    },
    "ch.verify.diagnostics_title": {
        "pl": "Diagnostyka",
        "en": "Diagnostics",
    },

    # ----- help long -----
    "help.long.ch": {
        "pl": (
            "ch <sub> [args] - playground Curry-Howard.\n\n"
            "Trzy ortogonalne perspektywy tego samego obiektu:\n"
            "  - rachunek lambda (term),\n"
            "  - typ STLC / Lean (zdanie),\n"
            "  - dowod taktyczny (przepis na term).\n\n"
            "Dziewiec podkomend:\n\n"
            "  ch term <lambda>          inferuje typ + interpretacja jako dowod\n"
            "    przyklad:               ch term \\\\p. p   ->  alpha -> alpha\n\n"
            "  ch type <T>               znajduje lambda-term zamieszkujacy typ T\n"
            "    przyklad:               ch type 'P -> P'   ->  lambda p. p\n\n"
            "  ch lib [name]             katalog kombinatorow (id, K, S, B, C, Y, ...)\n"
            "    przyklad:               ch lib K           ->  karta kombinatora K\n\n"
            "  ch lean <lambda>          generuje twierdzenie Lean 4\n"
            "    przyklad:               ch lean \\\\f x. f x\n\n"
            "  ch from-lean <expr>       parsuje term Lean -> lambda + typ\n"
            "    przyklad:               ch from-lean 'fun p => p'\n\n"
            "  ch tactic [name]          encyklopedia 22 taktyk Lean\n"
            "    przyklad:               ch tactic intro\n\n"
            "  ch build <T>              interaktywny builder krok po kroku\n"
            "    przyklad:               ch build 'P -> P'\n\n"
            "  ch verify <theorem>       sprawdza twierdzenie w Leanie (LSP / inline)\n"
            "    przyklad:               ch verify 'theorem t (P : Prop) : P -> P :=\n"
            "                                       fun p => p'\n\n"
            "  ch explore [slug]         interaktywny walker po katalogu 12 twierdzen\n"
            "    przyklad:               ch explore id    ->  drzewo termu identycznosci\n"
            "    na zywo:                ch explore --live --src 'theorem t (P : Prop) : P -> P := fun p => p'\n"
            "    z pliku:                ch explore --live --file proof.lean --no-walker\n\n"
            "Typowe sciezki nauki:\n"
            "  1. Zacznij od katalogu:   ch lib  (zobacz, ktore termy maja imiona)\n"
            "  2. Wez konkretny:         ch lib id  ->  pelna karta\n"
            "  3. Sprawdz typ swojego:   ch term \\\\p. p\n"
            "  4. Odwroc kierunek:       ch type 'P -> P'\n"
            "  5. Zobacz w Leanie:       ch lean \\\\p. p\n"
            "  6. Poznaj taktyki:        ch tactic intro\n"
            "  7. Zbuduj dowod:          ch build 'P -> P'\n"
            "  8. Sprawdz w Leanie:      ch verify '<theorem>'\n\n"
            "Pelna dokumentacja:\n"
            "  docs/ch_curry_howard.md\n"
            "  docs/ch_tactics_reference.md\n"
            "  docs/ch_library_reference.md\n"
            "  docs/ch_explore.md\n"
            "  Rozdzial ksiazki 10d. Curry-Howard playground.\n"
        ),
        "en": (
            "ch <sub> [args] - Curry-Howard playground.\n\n"
            "Three orthogonal lenses on the same object:\n"
            "  - lambda calculus (term),\n"
            "  - STLC / Lean type (proposition),\n"
            "  - tactic proof (recipe for the term).\n\n"
            "Nine sub-commands:\n\n"
            "  ch term <lambda>          infer type + proof interpretation\n"
            "    example:                ch term \\\\p. p   ->  alpha -> alpha\n\n"
            "  ch type <T>               find a lambda-term inhabiting type T\n"
            "    example:                ch type 'P -> P'   ->  lambda p. p\n\n"
            "  ch lib [name]             catalogue of combinators (id, K, S, B, C, Y, ...)\n"
            "    example:                ch lib K           ->  K combinator card\n\n"
            "  ch lean <lambda>          generate a Lean 4 theorem\n"
            "    example:                ch lean \\\\f x. f x\n\n"
            "  ch from-lean <expr>       parse a Lean term -> lambda + type\n"
            "    example:                ch from-lean 'fun p => p'\n\n"
            "  ch tactic [name]          encyclopedia of 22 Lean tactics\n"
            "    example:                ch tactic intro\n\n"
            "  ch build <T>              interactive step-by-step proof builder\n"
            "    example:                ch build 'P -> P'\n\n"
            "  ch verify <theorem>       check a theorem in Lean (LSP / inline)\n"
            "    example:                ch verify 'theorem t (P : Prop) : P -> P :=\n"
            "                                       fun p => p'\n\n"
            "  ch explore [slug]         interactive walker over a curated 12-theorem catalogue\n"
            "    example:                ch explore id    ->  identity proof term tree\n"
            "    live mode:              ch explore --live --src 'theorem t (P : Prop) : P -> P := fun p => p'\n"
            "    from file:              ch explore --live --file proof.lean --no-walker\n\n"
            "Typical learning paths:\n"
            "  1. Start with the catalogue:  ch lib  (see which terms have names)\n"
            "  2. Pick one:                  ch lib id  ->  full card\n"
            "  3. Check the type of yours:   ch term \\\\p. p\n"
            "  4. Reverse the direction:     ch type 'P -> P'\n"
            "  5. See it in Lean:            ch lean \\\\p. p\n"
            "  6. Meet the tactics:          ch tactic intro\n"
            "  7. Build a proof:             ch build 'P -> P'\n"
            "  8. Verify it in Lean:         ch verify '<theorem>'\n\n"
            "Full documentation:\n"
            "  docs/en/ch_curry_howard.md\n"
            "  docs/en/ch_tactics_reference.md\n"
            "  docs/en/ch_library_reference.md\n"
            "  docs/en/ch_explore.md\n"
            "  Book chapter 10d. Curry-Howard playground.\n"
        ),
    },

    # ============================================================
    # Tour: hub & shared scaffolding (`tour list`, `tour all`, etc.)
    # ============================================================
    "tour.entering": {
        "pl": "Wchodzimy w wycieczkę: [brand]{title}[/brand]. ENTER = dalej, --no-wait pomija pauzy.",
        "en": "Entering tour: [brand]{title}[/brand]. ENTER = next; --no-wait skips pauses.",
    },
    "tour.unknown": {
        "pl": "Nie znam wycieczki o nazwie '{name}'. Zobacz listę poniżej.",
        "en": "I do not know a tour called '{name}'. See the list below.",
    },
    "tour.demo_skipped_title": {
        "pl": "Demo pominięte",
        "en": "Demo skipped",
    },
    "tour.demo_failed": {
        "pl": "Demo nie zadziałało: {error}",
        "en": "The demo did not run: {error}",
    },
    "tour.demo_unknown_cmd": {
        "pl": "Nieznana komenda w skrypcie wycieczki: {cmd}",
        "en": "Unknown command in tour script: {cmd}",
    },
    "tour.list.header": {
        "pl": "Wycieczki Lambda Lab",
        "en": "Lambda Lab tours",
    },
    "tour.list.col.name": {
        "pl": "Nazwa",
        "en": "Name",
    },
    "tour.list.col.steps": {
        "pl": "Kroki",
        "en": "Steps",
    },
    "tour.list.col.summary": {
        "pl": "O czym",
        "en": "What it covers",
    },
    "tour.list.usage_hint": {
        "pl": "Uruchom: tour <nazwa> · tour <nazwa> --no-wait · tour all",
        "en": "Run: tour <name> · tour <name> --no-wait · tour all",
    },
    "tour.all.title": {
        "pl": "Wszystkie wycieczki po kolei",
        "en": "All tours, one after another",
    },
    "tour.all.intro": {
        "pl": (
            "Za chwilę uruchomię wszystkie 10 wycieczek po kolei. To może zająć\n"
            "około 15 minut — najlepiej z --no-wait do nagrania ekranu.\n"
            "Każda wycieczka ma własne wprowadzenie."
        ),
        "en": (
            "I am about to run all 10 tours back-to-back. This takes around\n"
            "15 minutes — best paired with --no-wait for screen recording.\n"
            "Each tour has its own intro."
        ),
    },

    # ============================================================
    # Tour: per-tour titles & summaries
    # ============================================================
    "tour.general.title": {
        "pl": "Wycieczka ogólna — od krokodyli do AlphaGeometry",
        "en": "General tour — from alligators to AlphaGeometry",
    },
    "tour.general.summary": {
        "pl": "Pełen łuk dydaktyczny: wtyczki, β, Church, Curry-Howard, Lean, AG",
        "en": "Full pedagogic arc: plugs, beta, Church, Curry-Howard, Lean, AG",
    },
    # Aliasy historyczne general.* (tour.step.<n>.* są równoważne tour.general.step.<n>.*).
    "tour.general.step.1.title": {
        "pl": "1. Wtyczki, kable i paczki",
        "en": "1. Plugs, cables and parcels",
    },
    "tour.general.step.1.body": {
        "pl": (
            "Amazon używa języka Dafny, opartego na matematycznym rachunku,\n"
            "żeby formalnie weryfikować, że algorytm sortowania paczek jest poprawny.\n"
            "Ta matematyka pochodzi z lat 40. XX wieku — to **rachunek λ**."
        ),
        "en": (
            "Amazon uses Dafny, a language built on a mathematical calculus,\n"
            "to formally verify that its parcel-sorting algorithm is correct.\n"
            "That mathematics goes back to the 1940s — it is the **lambda calculus**."
        ),
    },

    "tour.lambda.title": {
        "pl": "λ od środka — parser, β, α, η, postać normalna",
        "en": "Lambda internals — parser, beta, alpha, eta, normal form",
    },
    "tour.lambda.summary": {
        "pl": "Wnętrze rachunku: AST, ślad β, α-konwersja, dywergencja, kombinator Y",
        "en": "Calculus internals: AST, beta trace, alpha conversion, divergence, Y",
    },
    "tour.lambda.step.1.title": {
        "pl": "1. Parser i drzewo AST",
        "en": "1. Parser and AST tree",
    },
    "tour.lambda.step.1.body": {
        "pl": (
            "λ-term to drzewo: zmienne, abstrakcje (\\x. ...), aplikacje (f x).\n"
            "Komenda `lam` parsuje wyrażenie i pokazuje strukturę plus zmienne wolne.\n"
            "Zaraz zobaczysz `\\x y. x (y z)` — z = wolna, x i y = związane."
        ),
        "en": (
            "A lambda term is a tree: variables, abstractions (\\x. ...), applications (f x).\n"
            "The `lam` command parses an expression and prints structure plus free variables.\n"
            "You are about to see `\\x y. x (y z)` — z is free, x and y are bound."
        ),
    },
    "tour.lambda.step.2.title": {
        "pl": "2. β-redukcja krok po kroku",
        "en": "2. Beta-reduction step by step",
    },
    "tour.lambda.step.2.body": {
        "pl": (
            "(\\x. t) u → t[x := u]. Komenda `reduce` pokazuje każdy krok\n"
            "i podświetla redex. Klasyk: (\\x. x x)(\\y. y) — funkcja, która\n"
            "stosuje swój argument do siebie samego, na argumencie identyczności."
        ),
        "en": (
            "(\\x. t) u -> t[x := u]. The `reduce` command shows every step\n"
            "and highlights the redex. A classic: (\\x. x x)(\\y. y) — a function\n"
            "that applies its argument to itself, with identity as the argument."
        ),
    },
    "tour.lambda.step.3.title": {
        "pl": "3. α-konwersja: zmiana nazw zmiennych",
        "en": "3. Alpha-conversion: renaming bound variables",
    },
    "tour.lambda.step.3.body": {
        "pl": (
            "Dwie zmienne o tej samej nazwie w zagnieżdżonych abstrakcjach mogą\n"
            "się przesłaniać. Pretty-printer (`pretty(..., rename=True)`) automatycznie\n"
            "renumeruje, żeby wszystko było jednoznaczne. `\\x. \\x. x` po renamingu\n"
            "pokazuje, że wewnętrzne x przesłania zewnętrzne."
        ),
        "en": (
            "Two variables with the same name in nested abstractions may shadow each other.\n"
            "The pretty-printer (`pretty(..., rename=True)`) automatically renumbers\n"
            "to make everything unambiguous. `\\x. \\x. x` after renaming shows\n"
            "that the inner x shadows the outer one."
        ),
    },
    "tour.lambda.step.4.title": {
        "pl": "4. η-redukcja: \\x. f x ≡ f",
        "en": "4. Eta-reduction: \\x. f x ≡ f",
    },
    "tour.lambda.step.4.body": {
        "pl": (
            "Jeśli x nie występuje wolno w f, to (\\x. f x) jest równa f.\n"
            "Tutaj zobaczymy redukcję `(\\x. f x) y` — wstawiamy y za x i dostajemy f y."
        ),
        "en": (
            "If x is not free in f, then (\\x. f x) equals f.\n"
            "Here we will reduce `(\\x. f x) y` — we substitute y for x and obtain f y."
        ),
    },
    "tour.lambda.step.5.title": {
        "pl": "5. Postać normalna a dywergencja: OMEGA",
        "en": "5. Normal form vs divergence: OMEGA",
    },
    "tour.lambda.step.5.body": {
        "pl": (
            "Nie każdy term ma postać normalną. OMEGA = (\\x. x x)(\\x. x x) redukuje\n"
            "się do siebie samego — pętla nieskończona. Tracer ma cap (max_steps=80),\n"
            "więc nie zamrozi terminala — zobaczysz ostrzeżenie zamiast hangu.\n"
            "Spróbuj samodzielnie: `reduce (\\x. x x)(\\x. x x)` po wycieczce."
        ),
        "en": (
            "Not every term has a normal form. OMEGA = (\\x. x x)(\\x. x x) reduces\n"
            "to itself — an infinite loop. The tracer has a cap (max_steps=80),\n"
            "so it will not freeze your terminal — you will see a warning instead.\n"
            "Try it yourself: `reduce (\\x. x x)(\\x. x x)` after the tour."
        ),
    },
    "tour.lambda.step.6.title": {
        "pl": "6. Rekursja przez kombinator Y",
        "en": "6. Recursion through the Y-combinator",
    },
    "tour.lambda.step.6.body": {
        "pl": (
            "Y = \\f. (\\x. f (x x))(\\x. f (x x)). Y f rozwija się do f (Y f) —\n"
            "magia samopowtarzania bez wbudowanej rekursji.\n"
            "`church Y` rozwija stałą do dosłownej formy."
        ),
        "en": (
            "Y = \\f. (\\x. f (x x))(\\x. f (x x)). Y f unfolds to f (Y f) —\n"
            "self-replication magic without any built-in recursion.\n"
            "`church Y` expands the constant to its literal form."
        ),
    },

    "tour.church.title": {
        "pl": "Kodowania Churcha — boole, liczby, pary",
        "en": "Church encodings — booleans, numerals, pairs",
    },
    "tour.church.summary": {
        "pl": "TRUE/FALSE, AND/OR/NOT, NAND/XOR, liczby, PLUS/MULT/POW, EQ, PAIR/FST/SND",
        "en": "TRUE/FALSE, AND/OR/NOT, NAND/XOR, numerals, PLUS/MULT/POW, EQ, PAIR/FST/SND",
    },
    "tour.church.step.1.title": {
        "pl": "1. TRUE i FALSE — selektory",
        "en": "1. TRUE and FALSE — selectors",
    },
    "tour.church.step.1.body": {
        "pl": (
            "TRUE = \\t f. t — wybiera pierwszy argument.\n"
            "FALSE = \\t f. f — wybiera drugi.\n"
            "Cała logika boolowska wynika z tych dwóch wyborów."
        ),
        "en": (
            "TRUE = \\t f. t — picks the first argument.\n"
            "FALSE = \\t f. f — picks the second.\n"
            "All boolean logic flows from these two choices."
        ),
    },
    "tour.church.step.2.title": {
        "pl": "2. AND, OR, NOT — bazowe spójniki",
        "en": "2. AND, OR, NOT — base connectives",
    },
    "tour.church.step.2.body": {
        "pl": (
            "AND p q = p q p (jeśli p prawdziwe — zwraca q, inaczej p czyli FALSE).\n"
            "OR p q = p p q. NOT p = p FALSE TRUE.\n"
            "Po rozwinięciu i β-redukcji `church AND TRUE FALSE` daje FALSE."
        ),
        "en": (
            "AND p q = p q p (if p is true — return q, otherwise p i.e. FALSE).\n"
            "OR p q = p p q. NOT p = p FALSE TRUE.\n"
            "After expansion and beta-reduction, `church AND TRUE FALSE` yields FALSE."
        ),
    },
    "tour.church.step.3.title": {
        "pl": "3. Pochodne: NAND, NOR, XOR, XNOR, IMPLIES",
        "en": "3. Derived: NAND, NOR, XOR, XNOR, IMPLIES",
    },
    "tour.church.step.3.body": {
        "pl": (
            "Stałe pochodne mają **pojęciową** definicję, np. NAND p q ≡ NOT (AND p q).\n"
            "Komenda `church` najpierw rozwija nazwy do pełnych λ-form, potem β-redukuje.\n"
            "Tutaj pokażę NAND TRUE TRUE → FALSE."
        ),
        "en": (
            "Derived constants have a **conceptual** definition, e.g. NAND p q ≡ NOT (AND p q).\n"
            "The `church` command first expands names to full lambda forms, then beta-reduces.\n"
            "Here we show NAND TRUE TRUE -> FALSE."
        ),
    },
    "tour.church.step.4.title": {
        "pl": "4. Liczby Churcha 0-5",
        "en": "4. Church numerals 0-5",
    },
    "tour.church.step.4.body": {
        "pl": (
            "Liczba n to „n-krotne złożenie funkcji”:\n"
            "0 = \\f x. x, 1 = \\f x. f x, 2 = \\f x. f (f x), 3 = \\f x. f (f (f x))…\n"
            "`church 3` pokaże dosłowny term."
        ),
        "en": (
            "The number n means \"compose a function n times\":\n"
            "0 = \\f x. x, 1 = \\f x. f x, 2 = \\f x. f (f x), 3 = \\f x. f (f (f x))…\n"
            "`church 3` will show the literal term."
        ),
    },
    "tour.church.step.5.title": {
        "pl": "5. PLUS, MULT, POW",
        "en": "5. PLUS, MULT, POW",
    },
    "tour.church.step.5.body": {
        "pl": (
            "PLUS m n = \\f x. m f (n f x) — sklej dwa łańcuchy złożeń.\n"
            "MULT m n f = m (n f) — n-krotnie m-krotne złożenie.\n"
            "POW m n = n m — n-krotnie zastosuj m do bazy.\n"
            "`church PLUS 2 3` daje 5."
        ),
        "en": (
            "PLUS m n = \\f x. m f (n f x) — concatenate two chains of composition.\n"
            "MULT m n f = m (n f) — n-times-m composition.\n"
            "POW m n = n m — apply m n times to a base.\n"
            "`church PLUS 2 3` yields 5."
        ),
    },
    "tour.church.step.6.title": {
        "pl": "6. Predykaty: ISZERO, LEQ, EQ",
        "en": "6. Predicates: ISZERO, LEQ, EQ",
    },
    "tour.church.step.6.body": {
        "pl": (
            "ISZERO n = n (\\_. FALSE) TRUE. LEQ m n ≡ ISZERO (SUB m n).\n"
            "EQ m n ≡ AND (LEQ m n) (LEQ n m).\n"
            "`church EQ 2 2` daje TRUE — i to wszystko bez znaków równości w meta-języku."
        ),
        "en": (
            "ISZERO n = n (\\_. FALSE) TRUE. LEQ m n ≡ ISZERO (SUB m n).\n"
            "EQ m n ≡ AND (LEQ m n) (LEQ n m).\n"
            "`church EQ 2 2` yields TRUE — and all of it with no equality in the meta-language."
        ),
    },
    "tour.church.step.7.title": {
        "pl": "7. Pary: PAIR, FST, SND",
        "en": "7. Pairs: PAIR, FST, SND",
    },
    "tour.church.step.7.body": {
        "pl": (
            "PAIR a b = \\f. f a b — zamknięcie nad selektorem.\n"
            "FST = \\p. p TRUE (zastosuj parę do TRUE = wybierz pierwsze).\n"
            "SND = \\p. p FALSE.\n"
            "`church FST (PAIR 1 2)` daje 1."
        ),
        "en": (
            "PAIR a b = \\f. f a b — a closure over a selector.\n"
            "FST = \\p. p TRUE (apply the pair to TRUE = pick the first).\n"
            "SND = \\p. p FALSE.\n"
            "`church FST (PAIR 1 2)` yields 1."
        ),
    },

    "tour.peano.title": {
        "pl": "Arytmetyka Peano przez Church",
        "en": "Peano arithmetic via Church",
    },
    "tour.peano.summary": {
        "pl": "succ, pred, plus, mult, sub (clipped), leq, eq — wszystko bez liczb!",
        "en": "succ, pred, plus, mult, sub (clipped), leq, eq — all of it without numbers!",
    },
    "tour.peano.step.1.title": {
        "pl": "1. succ i pred",
        "en": "1. succ and pred",
    },
    "tour.peano.step.1.body": {
        "pl": (
            "Peano: każda liczba to 0 lub succ poprzedniej.\n"
            "pred (succ (succ 0)) = 1. Komenda `peano` ma alias dla nazw\n"
            "(succ → SUCC, pred → PRED) i rozwija przez Church + β."
        ),
        "en": (
            "Peano: every number is 0 or succ of the previous one.\n"
            "pred (succ (succ 0)) = 1. The `peano` command aliases names\n"
            "(succ -> SUCC, pred -> PRED) and expands through Church + beta."
        ),
    },
    "tour.peano.step.2.title": {
        "pl": "2. plus — rekursja kontra iteracja",
        "en": "2. plus — recursion vs iteration",
    },
    "tour.peano.step.2.body": {
        "pl": (
            "PLUS jest definiowane przez iterację, nie rekursję: m i n to **liczba zastosowań**\n"
            "funkcji, więc PLUS m n = funkcja stosowana (m+n) razy. `peano plus 2 3` = 5."
        ),
        "en": (
            "PLUS is defined by iteration, not recursion: m and n are **counts of applications**\n"
            "of a function, so PLUS m n = the function applied (m+n) times. `peano plus 2 3` = 5."
        ),
    },
    "tour.peano.step.3.title": {
        "pl": "3. mult",
        "en": "3. mult",
    },
    "tour.peano.step.3.body": {
        "pl": (
            "MULT m n f = m (n f) — n-krotne złożenie zastosowane m razy. To dosłownie\n"
            "definicja mnożenia jako wielokrotnego dodawania, ale w języku iteracji.\n"
            "`peano times 3 4` = 12."
        ),
        "en": (
            "MULT m n f = m (n f) — n-fold composition applied m times. This is literally\n"
            "the definition of multiplication as repeated addition, in the language of iteration.\n"
            "`peano times 3 4` = 12."
        ),
    },
    "tour.peano.step.4.title": {
        "pl": "4. sub — odejmowanie obcięte do zera",
        "en": "4. sub — subtraction clipped to zero",
    },
    "tour.peano.step.4.body": {
        "pl": (
            "Liczby Churcha są nieujemne, więc sub 3 5 nie zwraca -2 — daje 0.\n"
            "SUB m n = n PRED m: n-krotnie zastosuj poprzednika do m. Gdy m się skończy,\n"
            "PRED 0 = 0 (bezpiecznik)."
        ),
        "en": (
            "Church numerals are non-negative, so sub 3 5 does not return -2 — it gives 0.\n"
            "SUB m n = n PRED m: apply predecessor n times to m. When m runs out,\n"
            "PRED 0 = 0 (safety stop)."
        ),
    },
    "tour.peano.step.5.title": {
        "pl": "5. leq, eq — porównania",
        "en": "5. leq, eq — comparisons",
    },
    "tour.peano.step.5.body": {
        "pl": (
            "LEQ m n ≡ ISZERO (SUB m n). EQ m n ≡ AND (LEQ m n) (LEQ n m).\n"
            "Każde porównanie sprowadza się do odejmowania i sprawdzania zera."
        ),
        "en": (
            "LEQ m n ≡ ISZERO (SUB m n). EQ m n ≡ AND (LEQ m n) (LEQ n m).\n"
            "Every comparison reduces to subtraction plus checking for zero."
        ),
    },
    "tour.peano.step.6.title": {
        "pl": "6. Dlaczego to wszystko jest skończone",
        "en": "6. Why all of this stays finite",
    },
    "tour.peano.step.6.body": {
        "pl": (
            "Każda Church-liczba n koduje **dokładnie n** zastosowań funkcji. Gdy obliczasz\n"
            "PLUS 2 3, β-redukcja kończy się po skończonej liczbie kroków — nie ma\n"
            "implicit pętli, jest tylko skończone rozwijanie. Stąd terminale nie zwisają."
        ),
        "en": (
            "Each Church numeral n encodes **exactly n** applications of a function. When you\n"
            "compute PLUS 2 3, beta-reduction terminates after finitely many steps — there is no\n"
            "implicit loop, only finite unfolding. That is why the terminal never hangs."
        ),
    },

    "tour.prove.title": {
        "pl": "Automatyczny prover — tablice prawdy + IF-FUSION",
        "en": "Automatic prover — truth tables + IF-FUSION",
    },
    "tour.prove.summary": {
        "pl": "Katalog twierdzeń, weryfikacja przez 2^n wartościowań, dowód symboliczny",
        "en": "Theorem catalogue, verification across 2^n valuations, symbolic proof",
    },
    "tour.prove.step.1.title": {
        "pl": "1. Katalog twierdzeń",
        "en": "1. Theorem catalogue",
    },
    "tour.prove.step.1.body": {
        "pl": (
            "`prove list` pokazuje 14 wbudowanych tautologii: De Morgan, indukcja zera,\n"
            "rozdzielność, modus ponens, kombinator S Hilberta… Każde ma slug do uruchomienia."
        ),
        "en": (
            "`prove list` shows 14 built-in tautologies: De Morgan, double negation,\n"
            "distributivity, modus ponens, Hilbert's S combinator… Each has a slug to run."
        ),
    },
    "tour.prove.step.2.title": {
        "pl": "2. De Morgan przez tablicę prawdy",
        "en": "2. De Morgan via truth table",
    },
    "tour.prove.step.2.body": {
        "pl": (
            "`prove demorgan1` weryfikuje !(p AND q) = (!p OR !q) na wszystkich 4 wartościowaniach.\n"
            "Każda kolumna jest β-redukowana do TRUE/FALSE i porównywana."
        ),
        "en": (
            "`prove demorgan1` verifies !(p AND q) = (!p OR !q) across all 4 valuations.\n"
            "Each column is beta-reduced to TRUE/FALSE and compared."
        ),
    },
    "tour.prove.step.3.title": {
        "pl": "3. De Morgan przez IF-FUSION (symbolicznie)",
        "en": "3. De Morgan via IF-FUSION (symbolic)",
    },
    "tour.prove.step.3.body": {
        "pl": (
            "Z flagą `--fusion` prover robi rozwinięcie Shannona (case-split po zmiennej)\n"
            "i upraszcza IF-y. Wynik: dowód niezależny od liczby zmiennych — symboliczny."
        ),
        "en": (
            "With `--fusion` the prover performs Shannon expansion (case-split on a variable)\n"
            "and simplifies the IF terms. Result: a proof independent of how many variables — symbolic."
        ),
    },
    "tour.prove.step.4.title": {
        "pl": "4. Własna formuła",
        "en": "4. Custom formula",
    },
    "tour.prove.step.4.body": {
        "pl": (
            "Możesz podać dowolną formułę: `prove A AND B IMPLIES A`.\n"
            "Parser akceptuje AND/OR/NOT/IMPLIES, zmienne wielkimi literami."
        ),
        "en": (
            "You can pass any formula: `prove A AND B IMPLIES A`.\n"
            "The parser accepts AND/OR/NOT/IMPLIES, variables in capitals."
        ),
    },
    "tour.prove.step.5.title": {
        "pl": "5. Kontrprzykład — gdy to NIE jest tautologia",
        "en": "5. Counter-example — when it is NOT a tautology",
    },
    "tour.prove.step.5.body": {
        "pl": (
            "`prove A IMPLIES B` nie jest tautologią. Prover znajduje wartościowanie\n"
            "(A=TRUE, B=FALSE), które łamie formułę, i raportuje je."
        ),
        "en": (
            "`prove A IMPLIES B` is not a tautology. The prover finds a valuation\n"
            "(A=TRUE, B=FALSE) that breaks the formula and reports it."
        ),
    },
    "tour.prove.step.6.title": {
        "pl": "6. Klejnoty: excluded_middle, modus_ponens, hilbert_s",
        "en": "6. Highlights: excluded_middle, modus_ponens, hilbert_s",
    },
    "tour.prove.step.6.body": {
        "pl": (
            "`prove excluded_middle` (P OR NOT P), `prove modus_ponens` ((P AND (P→Q))→Q)\n"
            "i `prove hilbert_s` ((P→Q→R)→(P→Q)→P→R) — fundament logiki klasycznej."
        ),
        "en": (
            "`prove excluded_middle` (P OR NOT P), `prove modus_ponens` ((P AND (P->Q))->Q)\n"
            "and `prove hilbert_s` ((P->Q->R)->(P->Q)->P->R) — the bedrock of classical logic."
        ),
    },

    "tour.lean.title": {
        "pl": "Lean 4 — od and_comm po Erdősa",
        "en": "Lean 4 — from and_comm to Erdos",
    },
    "tour.lean.summary": {
        "pl": "Dema Lean: and_comm, NNG, Macbeth, Erdős #728, term proofs, arist server",
        "en": "Lean demos: and_comm, NNG, Macbeth, Erdos #728, term proofs, arist server",
    },
    "tour.lean.step.1.title": {
        "pl": "1. Wstęp — projekt lean_aristotle/",
        "en": "1. Intro — the lean_aristotle/ project",
    },
    "tour.lean.step.1.body": {
        "pl": (
            "Lean 4 + Mathlib v4.28 leżą w katalogu lambda_lab/proofs/lean_aristotle/.\n"
            "Komenda `lean <demo>` pokazuje plik źródłowy i (gdy jest lake) odpala kompilator.\n"
            "Bez Leana — pokaże offline ślad, więc zawsze zobaczysz coś sensownego."
        ),
        "en": (
            "Lean 4 + Mathlib v4.28 sit in lambda_lab/proofs/lean_aristotle/.\n"
            "The `lean <demo>` command shows the source and (when lake is around) runs the compiler.\n"
            "Without Lean — it shows an offline trace, so you always see something meaningful."
        ),
    },
    "tour.lean.step.2.title": {
        "pl": "2. and_comm — pierwszy dowód",
        "en": "2. and_comm — the first proof",
    },
    "tour.lean.step.2.body": {
        "pl": (
            "`lean and_comm` pokazuje dowód `p ∧ q ↔ q ∧ p`. Cztery linie taktyk\n"
            "(intro, exact, And.intro), kernel-checked. To Twój pierwszy kontakt z Leanem."
        ),
        "en": (
            "`lean and_comm` shows a proof of `p ∧ q ↔ q ∧ p`. Four lines of tactics\n"
            "(intro, exact, And.intro), kernel-checked. Your first hand-shake with Lean."
        ),
    },
    "tour.lean.step.3.title": {
        "pl": "3. NNG — indukcja w akcji",
        "en": "3. NNG — induction in action",
    },
    "tour.lean.step.3.body": {
        "pl": (
            "Natural Number Game — gra Kevin Buzzarda do nauki Leana. `lean nng`\n"
            "pokazuje add_comm dla liczb naturalnych przez indukcję. Tradycyjny przykład."
        ),
        "en": (
            "Natural Number Game — Kevin Buzzard's game for learning Lean. `lean nng`\n"
            "shows add_comm for natural numbers by induction. The classic example."
        ),
    },
    "tour.lean.step.4.title": {
        "pl": "4. Macbeth — bloki calc",
        "en": "4. Macbeth — calc blocks",
    },
    "tour.lean.step.4.body": {
        "pl": (
            "Heather Macbeth uczy Lean przez bloki `calc`: każdy krok to równanie\n"
            "z uzasadnieniem (`by ring`, `by linarith`). `lean macbeth` pokazuje przykład."
        ),
        "en": (
            "Heather Macbeth teaches Lean via `calc` blocks: each step is an equation\n"
            "with a justification (`by ring`, `by linarith`). `lean macbeth` shows an example."
        ),
    },
    "tour.lean.step.5.title": {
        "pl": "5. Erdős #728 — pierwszy problem rozwiązany przez AI",
        "en": "5. Erdos #728 — the first problem solved by AI",
    },
    "tour.lean.step.5.body": {
        "pl": (
            "Styczeń 2026: GPT-5.2 Pro + Aristotle autonomicznie znalazły dowód jednego\n"
            "z problemów z listy Erdősa. Tao zweryfikował. Preprint: arXiv 2601.07421.\n"
            "`lean erdos` pokaże szkic dowodu w naszym repo."
        ),
        "en": (
            "January 2026: GPT-5.2 Pro + Aristotle autonomously found a proof of one\n"
            "of the problems on Erdos's list. Tao verified it. Preprint: arXiv 2601.07421.\n"
            "`lean erdos` shows a sketch of the proof in our repo."
        ),
    },
    "tour.lean.step.6.title": {
        "pl": "6. arist server — szybki LSP",
        "en": "6. arist server — fast LSP",
    },
    "tour.lean.step.6.body": {
        "pl": (
            "Każda kompilacja Mathliba kosztuje 13 s — to za dużo dla iteracji.\n"
            "`arist server` trzyma proces Leana w tle, jako LSP. Pierwszy compile = 13 s,\n"
            "kolejne = pół sekundy. Po wycieczce: spróbuj `arist server` w osobnym oknie."
        ),
        "en": (
            "Every Mathlib compile costs 13 s — too slow for iteration.\n"
            "`arist server` keeps a Lean process running in the background, as LSP. First compile = 13 s,\n"
            "subsequent = half a second. After the tour: try `arist server` in a separate window."
        ),
    },

    "tour.ag.title": {
        "pl": "AlphaGeometry — geometria z DeepMind",
        "en": "AlphaGeometry — geometry from DeepMind",
    },
    "tour.ag.summary": {
        "pl": "DD+AR replay: angle bisector, isogonal, IMO P4 — paralela do Aristotle",
        "en": "DD+AR replay: angle bisector, isogonal, IMO P4 — parallel to Aristotle",
    },
    "tour.ag.step.1.title": {
        "pl": "1. Czym jest AlphaGeometry",
        "en": "1. What AlphaGeometry is",
    },
    "tour.ag.step.1.body": {
        "pl": (
            "AlphaGeometry (DeepMind) łączy LLM (do propozycji konstrukcji pomocniczych)\n"
            "z symbolicznym solverem DD+AR (Deductive Database + Algebraic Reasoning).\n"
            "Pokonała IMO 2024 P4 z auxiliary points, których człowiek nigdy by nie wymyślił."
        ),
        "en": (
            "AlphaGeometry (DeepMind) couples an LLM (proposing auxiliary constructions)\n"
            "with a symbolic DD+AR solver (Deductive Database + Algebraic Reasoning).\n"
            "It beat IMO 2024 P4 using auxiliary points that no human would have invented."
        ),
    },
    "tour.ag.step.2.title": {
        "pl": "2. Dwusieczna kąta = wysokość (replay)",
        "en": "2. Angle bisector = altitude (replay)",
    },
    "tour.ag.step.2.body": {
        "pl": (
            "`ag angle_bisector` odtwarza dowód, że w trójkącie równoramiennym\n"
            "dwusieczna kąta wierzchołka jest też wysokością. Każdy krok = jedna reguła DD."
        ),
        "en": (
            "`ag angle_bisector` replays the proof that in an isosceles triangle\n"
            "the apex angle bisector is also an altitude. Each step = one DD rule."
        ),
    },
    "tour.ag.step.3.title": {
        "pl": "3. Sprzężenie izogonalne — IMO 2024 sketch",
        "en": "3. Isogonal conjugation — IMO 2024 sketch",
    },
    "tour.ag.step.3.body": {
        "pl": (
            "`ag isogonal` pokazuje konstrukcję sprzężenia izogonalnego i okrąg.\n"
            "To szkic z dowodu jednego z zadań IMO 2024."
        ),
        "en": (
            "`ag isogonal` shows the isogonal conjugation construction and a circle.\n"
            "It is a sketch from one of the IMO 2024 problem proofs."
        ),
    },
    "tour.ag.step.4.title": {
        "pl": "4. IMO P4 — konstrukcja pomocnicza",
        "en": "4. IMO P4 — auxiliary construction",
    },
    "tour.ag.step.4.body": {
        "pl": (
            "`ag imo_p4` ilustruje, jak dodanie jednego punktu pomocniczego rozwiązuje\n"
            "zadanie. Algorytm AG sam wpadł na ten punkt — ludzie zwykle nie."
        ),
        "en": (
            "`ag imo_p4` shows how adding a single auxiliary point cracks the problem.\n"
            "The AG algorithm came up with that point on its own — humans usually do not."
        ),
    },
    "tour.ag.step.5.title": {
        "pl": "5. Aristotle ↔ AlphaGeometry",
        "en": "5. Aristotle <-> AlphaGeometry",
    },
    "tour.ag.step.5.body": {
        "pl": (
            "Aristotle = AI dla logiki / arytmetyki / Mathliba. AlphaGeometry = AI dla geometrii.\n"
            "Wspólny wzorzec: LLM proponuje, symboliczny silnik weryfikuje. To filozofia\n"
            "neurosymbolic AI w działaniu — i tak dziś matematyka spotyka uczenie maszynowe."
        ),
        "en": (
            "Aristotle = AI for logic / arithmetic / Mathlib. AlphaGeometry = AI for geometry.\n"
            "Shared pattern: the LLM proposes, the symbolic engine verifies. That is the\n"
            "neurosymbolic-AI philosophy in action — and how mathematics meets ML today."
        ),
    },

    "tour.arist.title": {
        "pl": "Aristotle workflow — od klucza do PDF",
        "en": "Aristotle workflow — from API key to PDF",
    },
    "tour.arist.summary": {
        "pl": "key, demo, list/watch, show/compile, --server/--cache, warmup, informal, pdf",
        "en": "key, demo, list/watch, show/compile, --server/--cache, warmup, informal, pdf",
    },
    "tour.arist.step.1.title": {
        "pl": "1. Setup — `arist key`",
        "en": "1. Setup — `arist key`",
    },
    "tour.arist.step.1.body": {
        "pl": (
            "`arist key` pokazuje status kluczy: ARISTOTLE_API_KEY (do submisji)\n"
            "i OPENAI_API_KEY (do informal). Bez kluczy zobaczysz MISSING — nic złego się nie stanie."
        ),
        "en": (
            "`arist key` shows the status of keys: ARISTOTLE_API_KEY (for submissions)\n"
            "and OPENAI_API_KEY (for informal). Without keys you will see MISSING — nothing breaks."
        ),
    },
    "tour.arist.step.2.title": {
        "pl": "2. Submit — `arist demo`",
        "en": "2. Submit — `arist demo`",
    },
    "tour.arist.step.2.body": {
        "pl": (
            "`arist demo` wysyła twierdzenie De Morgana do Aristotle (potrzebny klucz API).\n"
            "Dostajesz `project_id` — identyfikator do późniejszego śledzenia.\n"
            "Bez sieci/klucza demo będzie pominięte — pokażę dalej resztę pipeline'u."
        ),
        "en": (
            "`arist demo` sends De Morgan's theorem to Aristotle (API key required).\n"
            "You get a `project_id` — an identifier to track later.\n"
            "Without network/key the demo will be skipped — I show the rest of the pipeline anyway."
        ),
    },
    "tour.arist.step.3.title": {
        "pl": "3. List & Watch",
        "en": "3. List & Watch",
    },
    "tour.arist.step.3.body": {
        "pl": (
            "`arist list` — historia wszystkich projektów lokalnych.\n"
            "`arist watch <id>` — odpytuje serwer co kilka sekund i raportuje status\n"
            "(QUEUED → SOLVING → COMPLETED). To długi proces, więc warto pójść zaparzyć kawę."
        ),
        "en": (
            "`arist list` — the history of every local project.\n"
            "`arist watch <id>` — polls the server every few seconds and reports the status\n"
            "(QUEUED -> SOLVING -> COMPLETED). It is a long process — go grab coffee."
        ),
    },
    "tour.arist.step.4.title": {
        "pl": "4. Show & Compile",
        "en": "4. Show & Compile",
    },
    "tour.arist.step.4.body": {
        "pl": (
            "`arist show <id>` — wyświetla zwrócony plik `.lean`.\n"
            "`arist compile <id>` — kompiluje go lokalnie (Mathlib + Lean 4).\n"
            "Pierwszy compile bez serwera trwa ~13 s (deserializacja olean-ów Mathliba)."
        ),
        "en": (
            "`arist show <id>` — display the returned `.lean` file.\n"
            "`arist compile <id>` — compile it locally (Mathlib + Lean 4).\n"
            "The first compile without a server takes ~13 s (deserializing Mathlib oleans)."
        ),
    },
    "tour.arist.step.5.title": {
        "pl": "5. Compile szybciej: --server i --cache",
        "en": "5. Compile faster: --server and --cache",
    },
    "tour.arist.step.5.body": {
        "pl": (
            "`arist compile --server <id>` używa LSP (`arist server` w innym oknie). Pół sekundy.\n"
            "`arist compile --cache <id>` używa lake build cache — kolejne kompilacje są tanie.\n"
            "Do iteracji nad jednym dowodem — bez tego się nie da."
        ),
        "en": (
            "`arist compile --server <id>` uses LSP (`arist server` in another window). Half a second.\n"
            "`arist compile --cache <id>` uses lake build cache — subsequent compiles are cheap.\n"
            "For iterating on a single proof — there is no other way."
        ),
    },
    "tour.arist.step.6.title": {
        "pl": "6. Warmup — heat the cache",
        "en": "6. Warmup — heat the cache",
    },
    "tour.arist.step.6.body": {
        "pl": (
            "`arist warmup` ładuje pliki olean Mathliba do page cache systemu (osobny wątek).\n"
            "Po nim pierwszy compile spada z 13 s do ~5 s. REPL robi to automatycznie przy starcie."
        ),
        "en": (
            "`arist warmup` loads Mathlib olean files into the OS page cache (separate thread).\n"
            "After that the first compile drops from 13 s to ~5 s. The REPL does it automatically on start."
        ),
    },
    "tour.arist.step.7.title": {
        "pl": "7. Informal — wyjaśnienie po ludzku",
        "en": "7. Informal — explanation in human language",
    },
    "tour.arist.step.7.body": {
        "pl": (
            "`arist informal <id>` wysyła zwrócony dowód Lean do GPT-5.5 i prosi\n"
            "o wyjaśnienie w Twoim języku (PL lub EN). Wynik to czytelna proza z\n"
            "kluczowymi krokami i intuicją."
        ),
        "en": (
            "`arist informal <id>` sends the returned Lean proof to GPT-5.5 and asks\n"
            "for an explanation in your language (PL or EN). The result is readable prose\n"
            "with key steps and intuitions."
        ),
    },
    "tour.arist.step.8.title": {
        "pl": "8. Eksport PDF",
        "en": "8. PDF export",
    },
    "tour.arist.step.8.body": {
        "pl": (
            "`arist pdf <id>` produkuje notatkę PDF: tytuł, sformułowanie, dowód Lean,\n"
            "wyjaśnienie informal. Idealne do wykładu lub do wpięcia w portfolio."
        ),
        "en": (
            "`arist pdf <id>` produces a PDF note: title, statement, Lean proof,\n"
            "informal explanation. Perfect for a lecture handout or a portfolio piece."
        ),
    },

    "tour.ch.title": {
        "pl": "Curry-Howard playground — ch w 8 podtrybach",
        "en": "Curry-Howard playground — `ch` in 8 sub-modes",
    },
    "tour.ch.summary": {
        "pl": "term, type, lib, lean, tactic, build, verify, from-lean — λ jako dowód",
        "en": "term, type, lib, lean, tactic, build, verify, from-lean — lambda as proof",
    },
    "tour.ch.step.1.title": {
        "pl": "1. Przegląd `ch`",
        "en": "1. `ch` overview",
    },
    "tour.ch.step.1.body": {
        "pl": (
            "`ch` bez argumentu pokazuje kartę z 8 podkomendami. Każda dotyka jednego\n"
            "aspektu izomorfizmu Curry-Howarda: λ-term = dowód, typ = twierdzenie, taktyka = krok."
        ),
        "en": (
            "`ch` without arguments shows a card with 8 sub-commands. Each touches one\n"
            "facet of the Curry-Howard isomorphism: lambda-term = proof, type = theorem, tactic = step."
        ),
    },
    "tour.ch.step.2.title": {
        "pl": "2. Biblioteka — `ch lib id`, `ch lib K`",
        "en": "2. Library — `ch lib id`, `ch lib K`",
    },
    "tour.ch.step.2.body": {
        "pl": (
            "`ch lib` katalog 12+ kanonicznych kombinatorów: id, K, S, B, C, Y, fst, snd…\n"
            "`ch lib id` pokazuje pełną kartę: λ-term, typ, dowód Lean, taktykowy szkic."
        ),
        "en": (
            "`ch lib` lists 12+ canonical combinators: id, K, S, B, C, Y, fst, snd…\n"
            "`ch lib id` shows a full card: lambda-term, type, Lean proof, tactic sketch."
        ),
    },
    "tour.ch.step.3.title": {
        "pl": "3. Inferencja typów — `ch term \\f g x. g (f x)`",
        "en": "3. Type inference — `ch term \\f g x. g (f x)`",
    },
    "tour.ch.step.3.body": {
        "pl": (
            "Algorytm Hindley-Milner-lite zgaduje typ z kształtu termu.\n"
            "Tutaj zobaczysz typ `(α → β) → (β → γ) → α → γ` — kompozycja."
        ),
        "en": (
            "A Hindley-Milner-lite algorithm guesses the type from the term's shape.\n"
            "Here you will see the type `(α → β) → (β → γ) → α → γ` — composition."
        ),
    },
    "tour.ch.step.4.title": {
        "pl": "4. Wyszukiwanie dowodu — `ch type 'P -> Q -> P'`",
        "en": "4. Proof search — `ch type 'P -> Q -> P'`",
    },
    "tour.ch.step.4.body": {
        "pl": (
            "Komenda `ch type` szuka termu o zadanym typie. `P -> Q -> P` ma jeden\n"
            "naturalny kandydat: `\\p q. p` — to kombinator K (constant)."
        ),
        "en": (
            "The `ch type` command searches for a term of a given type. `P -> Q -> P` has one\n"
            "natural candidate: `\\p q. p` — that is the K combinator (constant)."
        ),
    },
    "tour.ch.step.5.title": {
        "pl": "5. λ → Lean — `ch lean \\p. p`",
        "en": "5. lambda -> Lean — `ch lean \\p. p`",
    },
    "tour.ch.step.5.body": {
        "pl": (
            "`ch lean <term>` generuje pełen plik Lean z theorem + dowodem termowym.\n"
            "Działa w obie strony: `ch from-lean fun p => p` cofa do λ-termu."
        ),
        "en": (
            "`ch lean <term>` generates a full Lean file with a theorem and a term proof.\n"
            "It works both ways: `ch from-lean fun p => p` returns to the lambda-term."
        ),
    },
    "tour.ch.step.6.title": {
        "pl": "6. Encyklopedia taktyk — `ch tactic intro`",
        "en": "6. Tactic encyclopedia — `ch tactic intro`",
    },
    "tour.ch.step.6.body": {
        "pl": (
            "`ch tactic` lista 22 taktyk Lean z mapą na konstrukcje λ. `ch tactic intro`\n"
            "pokaże kartę: opis, efekt na celu, efekt na termie, kiedy stosować, mini-przykład."
        ),
        "en": (
            "`ch tactic` lists 22 Lean tactics with a map to lambda constructions. `ch tactic intro`\n"
            "shows a card: description, goal effect, term effect, when to use, mini-example."
        ),
    },
    "tour.ch.step.7.title": {
        "pl": "7. Interaktywny build — `ch build P -> P`",
        "en": "7. Interactive build — `ch build P -> P`",
    },
    "tour.ch.step.7.body": {
        "pl": (
            "`ch build` to interaktywny dialog: pokazujesz cel, prosisz o kolejne taktyki,\n"
            "a system buduje λ-term równolegle. Skrypt typowej sesji:\n"
            "  Cel: P -> P\n"
            "  > intro p     (cel: P; term: \\p. ?)\n"
            "  > exact p     (gotowe; term: \\p. p)\n"
            "Wewnątrz wycieczki nie odpalimy interaktywnie — opisujemy dialog. Spróbuj sam."
        ),
        "en": (
            "`ch build` is an interactive dialogue: you show the goal, ask for the next tactic,\n"
            "and the system builds the lambda term in parallel. Script of a typical session:\n"
            "  Goal: P -> P\n"
            "  > intro p     (goal: P; term: \\p. ?)\n"
            "  > exact p     (done; term: \\p. p)\n"
            "Inside a tour we do not run it interactively — we narrate the dialogue. Try it yourself."
        ),
    },
    "tour.ch.step.8.title": {
        "pl": "8. Verify — `ch verify`",
        "en": "8. Verify — `ch verify`",
    },
    "tour.ch.step.8.body": {
        "pl": (
            "`ch verify '<theorem>'` przepuszcza Twoje twierdzenie przez Lean (LSP lub inline).\n"
            "Wymaga lokalnego Leana — bez niego dostaniesz informację o backendzie i sugestię\n"
            "uruchomienia `arist server` w drugim oknie. To naturalny mostek do `arist`."
        ),
        "en": (
            "`ch verify '<theorem>'` runs your theorem through Lean (LSP or inline).\n"
            "Requires a local Lean — without it you get a backend message and a suggestion\n"
            "to run `arist server` in another window. A natural bridge to `arist`."
        ),
    },

    "tour.alligators.title": {
        "pl": "Alligator Eggs — gra Breta Victora",
        "en": "Alligator Eggs — Bret Victor's game",
    },
    "tour.alligators.summary": {
        "pl": "Figury, reguła jedzenia (β), reguła kolorów (α), reguła starości",
        "en": "Pieces, eating rule (beta), color rule (alpha), old-age rule",
    },
    "tour.alligators.step.1.title": {
        "pl": "1. Kanon figur",
        "en": "1. The canon of pieces",
    },
    "tour.alligators.step.1.body": {
        "pl": (
            "Bret Victor zamienił λ-rachunek w grę: kolorowe krokodyle (abstrakcje) zjadają\n"
            "rodziny (aplikacje), jajka (zmienne) wykluwają się w to, co krokodyl strzeże.\n"
            "Tutaj: TRUE = dwa krokodyle obejmujące jajko."
        ),
        "en": (
            "Bret Victor turned the lambda calculus into a game: coloured alligators (abstractions)\n"
            "eat families (applications), eggs (variables) hatch into whatever the alligator guards.\n"
            "Here: TRUE = two alligators wrapping an egg."
        ),
    },
    "tour.alligators.step.2.title": {
        "pl": "2. Reguła jedzenia (β)",
        "en": "2. Eating rule (beta)",
    },
    "tour.alligators.step.2.body": {
        "pl": (
            "Krokodyl po lewej zjada rodzinę po prawej, a jego jajka wykluwają się w tę rodzinę.\n"
            "To dosłownie β-redukcja. (\\x. x x)(\\y. y) — krokodyl-x zjada krokodyla-y\n"
            "i wszystkie jajka x wykluwają się w krokodyla-y."
        ),
        "en": (
            "The left alligator eats the right family, and its eggs hatch into that family.\n"
            "Literally beta-reduction. (\\x. x x)(\\y. y) — alligator-x eats alligator-y\n"
            "and every x egg hatches into alligator-y."
        ),
    },
    "tour.alligators.step.3.title": {
        "pl": "3. Reguła kolorów (α)",
        "en": "3. Color rule (alpha)",
    },
    "tour.alligators.step.3.body": {
        "pl": (
            "Dwa krokodyle tego samego koloru w zagnieżdżeniu zacierają tożsamość jajek.\n"
            "Dlatego zmieniamy kolor wewnętrznego (α-konwersja): `\\x. \\x. x` po\n"
            "renamingu daje jasną intuicję, które jajko wykluwa się w które."
        ),
        "en": (
            "Two same-coloured alligators in a nesting blur the identity of the eggs.\n"
            "So we recolour the inner one (alpha conversion): `\\x. \\x. x` after renaming\n"
            "gives a clear intuition which egg hatches into which."
        ),
    },
    "tour.alligators.step.4.title": {
        "pl": "4. Reguła starości — krokodyl umiera, jajko żyje",
        "en": "4. Old-age rule — alligator dies, egg lives",
    },
    "tour.alligators.step.4.body": {
        "pl": (
            "Gdy krokodyl ma tylko jedno jajko (i nic do zjedzenia), umiera ze starości:\n"
            "zostaje samo jajko. To eliminuje zbędne nawiasy. W λ: \\x. x sam w sobie\n"
            "to identity — i nic poza nią."
        ),
        "en": (
            "When an alligator has only one egg (and nothing to eat), it dies of old age:\n"
            "the egg is left alone. This eliminates superfluous brackets. In lambda: \\x. x\n"
            "by itself is the identity — and nothing more."
        ),
    },

    # ============================================================
    # Knowledge Base (`kb` command) -- curated literature browser
    # ============================================================
    "cmd.kb": {
        "pl": "baza wiedzy: ~120 pozycji, 16 tematów, 7 ścieżek czytelniczych",
        "en": "knowledge base: ~120 entries, 16 topics, 7 reading bundles",
    },

    # ----- top-level overview panel -----
    "kb.overview.title": {
        "pl": "Knowledge Base — przewodnik po literaturze",
        "en": "Knowledge Base -- a literature companion",
    },
    "kb.overview.body": {
        "pl": (
            "Skuratowana biblioteka materiałów do rachunku λ, teorii typów,\n"
            "Curry-Howarda, Lean 4 i AI-matematyki. Polecane wejścia:\n\n"
            "  * `kb topics`                — pełna lista tematów\n"
            "  * `kb topic combinators`     — głęboki nurek w kombinatory\n"
            "  * `kb topic inductive-types` — głęboki nurek w typy indukcyjne\n"
            "  * `kb bundles`               — gotowe ścieżki czytelnicze\n"
            "  * `kb random`                — losowa rekomendacja\n"
            "  * `kb search Curry-Howard`   — wyszukiwarka\n\n"
            "Wpisz `help kb` po pełne komendy."
        ),
        "en": (
            "Curated library for lambda calculus, type theory, Curry-Howard,\n"
            "Lean 4 and AI-driven mathematics. Suggested entry points:\n\n"
            "  * `kb topics`                -- list every topic\n"
            "  * `kb topic combinators`     -- deep dive into combinators\n"
            "  * `kb topic inductive-types` -- deep dive into inductive types\n"
            "  * `kb bundles`               -- curated reading paths\n"
            "  * `kb random`                -- random recommendation\n"
            "  * `kb search Curry-Howard`   -- full-text search\n\n"
            "Type `help kb` for the full command reference."
        ),
    },

    # ----- generic columns / labels -----
    "kb.col.id":         {"pl": "ID", "en": "ID"},
    "kb.col.kind":       {"pl": "Rodzaj", "en": "Kind"},
    "kb.col.difficulty": {"pl": "Trudność", "en": "Difficulty"},
    "kb.col.year":       {"pl": "Rok", "en": "Year"},
    "kb.col.title":      {"pl": "Tytuł", "en": "Title"},
    "kb.col.authors":    {"pl": "Autorzy", "en": "Authors"},
    "kb.col.canonical":  {"pl": "Kan.", "en": "Can."},
    "kb.col.step":       {"pl": "Krok", "en": "Step"},
    "kb.col.count":      {"pl": "Liczba", "en": "Count"},
    "kb.col.topic":      {"pl": "Temat", "en": "Topic"},
    "kb.col.bundle":     {"pl": "Ścieżka", "en": "Bundle"},
    "kb.col.resources":  {"pl": "Pozycje", "en": "Resources"},
    "kb.col.audience":   {"pl": "Adresaci", "en": "Audience"},
    "kb.col.hours":      {"pl": "Godziny", "en": "Hours"},
    "kb.col.description":{"pl": "Opis", "en": "Description"},

    # ----- topics list -----
    "kb.topics.title": {
        "pl": "Tematy w bazie wiedzy",
        "en": "Topics in the knowledge base",
    },
    "kb.topics.empty": {
        "pl": "Brak tematów. Sprawdź `lambda_lab/lab/kb/data/topics/`.",
        "en": "No topics found. Check `lambda_lab/lab/kb/data/topics/`.",
    },

    # ----- topic detail -----
    "kb.topic.usage": {
        "pl": "Użycie: kb topic <id>. Np. `kb topic combinators`.",
        "en": "Usage: kb topic <id>. Example: `kb topic combinators`.",
    },
    "kb.topic.unknown": {
        "pl": "Nieznany temat: {topic}. Spróbuj `kb topics`.",
        "en": "Unknown topic: {topic}. Try `kb topics`.",
    },
    "kb.topic.no_resources": {
        "pl": "Temat nie ma jeszcze przypisanych pozycji.",
        "en": "This topic has no resources yet.",
    },
    "kb.topic.resources_table_title": {
        "pl": "Polecane lektury (* = kanon)",
        "en": "Recommended readings (* = canon)",
    },
    "kb.topic.related_topics":  {"pl": "Powiązane tematy", "en": "Related topics"},
    "kb.topic.related_commands":{"pl": "Powiązane komendy REPL", "en": "Related REPL commands"},

    # ----- show resource -----
    "kb.show.usage": {
        "pl": "Użycie: kb show <id>. Lista: `kb topic <id>` lub `kb search ...`.",
        "en": "Usage: kb show <id>. Lists: `kb topic <id>` or `kb search ...`.",
    },
    "kb.show.unknown": {
        "pl": "Nieznana pozycja: {rid}. Spróbuj `kb search ...` lub `kb topic <id>`.",
        "en": "Unknown resource: {rid}. Try `kb search ...` or `kb topic <id>`.",
    },
    "kb.show.row.authors":    {"pl": "Autorzy", "en": "Authors"},
    "kb.show.row.year":       {"pl": "Rok", "en": "Year"},
    "kb.show.row.kind":       {"pl": "Rodzaj", "en": "Kind"},
    "kb.show.row.difficulty": {"pl": "Trudność", "en": "Difficulty"},
    "kb.show.row.license":    {"pl": "Licencja", "en": "License"},
    "kb.show.row.pages":      {"pl": "Strony", "en": "Pages"},
    "kb.show.row.topics":     {"pl": "Tematy", "en": "Topics"},
    "kb.show.row.tags":       {"pl": "Tagi", "en": "Tags"},
    "kb.show.row.pdf":        {"pl": "PDF lokalnie", "en": "Local PDF"},
    "kb.show.section.abstract":  {"pl": "Streszczenie", "en": "Abstract"},
    "kb.show.section.why":       {"pl": "Dlaczego ta pozycja", "en": "Why it is here"},
    "kb.show.section.prereqs":   {"pl": "Prerekwizyty", "en": "Prerequisites"},
    "kb.show.section.follow_up": {"pl": "Dalej", "en": "Follow-up"},
    "kb.show.open_prompt": {
        "pl": "Otworzyć zewnętrznie? [T/n] ",
        "en": "Open externally? [Y/n] ",
    },
    "kb.show.no_target": {
        "pl": "Brak URL/DOI/arXiv/ISBN — nie da się otworzyć.",
        "en": "No URL/DOI/arXiv/ISBN -- nothing to open.",
    },

    # ----- open command -----
    "kb.open.usage": {
        "pl": "Użycie: kb open <id>.",
        "en": "Usage: kb open <id>.",
    },
    "kb.open.unknown": {
        "pl": "Nieznana pozycja: {rid}.",
        "en": "Unknown resource: {rid}.",
    },
    "kb.open.opening": {
        "pl": "Otwieram: {target}",
        "en": "Opening: {target}",
    },
    "kb.open.failed": {
        "pl": "Nie udało się otworzyć: {error}",
        "en": "Could not open: {error}",
    },

    # ----- search -----
    "kb.search.usage": {
        "pl": "Użycie: kb search <słowo> [--topic <id>] [--kind paper,book] [--difficulty 1-3].",
        "en": "Usage: kb search <keyword> [--topic <id>] [--kind paper,book] [--difficulty 1-3].",
    },
    "kb.search.no_hits": {
        "pl": "Nic nie znaleziono dla: {kw}.",
        "en": "No matches for: {kw}.",
    },
    "kb.search.title": {
        "pl": "Wyniki wyszukiwania: {kw} ({count})",
        "en": "Search results for: {kw} ({count})",
    },

    # ----- random -----
    "kb.random.empty": {
        "pl": "Pusta baza wiedzy — nic nie wylosowałem.",
        "en": "Empty knowledge base -- nothing to recommend.",
    },
    "kb.random.title": {
        "pl": "Losowa rekomendacja",
        "en": "Random recommendation",
    },

    # ----- bundles -----
    "kb.bundles.title": {
        "pl": "Ścieżki czytelnicze",
        "en": "Reading bundles",
    },
    "kb.bundles.empty": {
        "pl": "Brak ścieżek — sprawdź `lambda_lab/lab/kb/data/bundles/`.",
        "en": "No bundles found -- check `lambda_lab/lab/kb/data/bundles/`.",
    },
    "kb.bundle.usage": {
        "pl": "Użycie: kb bundle <id>. Lista: `kb bundles`.",
        "en": "Usage: kb bundle <id>. Lists: `kb bundles`.",
    },
    "kb.bundle.unknown": {
        "pl": "Nieznana ścieżka: {bid}. Spróbuj `kb bundles`.",
        "en": "Unknown bundle: {bid}. Try `kb bundles`.",
    },
    "kb.bundle.audience":         {"pl": "Adresaci", "en": "Audience"},
    "kb.bundle.estimated_hours":  {"pl": "Szacowany czas", "en": "Estimated time"},
    "kb.bundle.reading_order":    {"pl": "Kolejność czytania", "en": "Reading order"},
    "kb.bundle.missing_resource": {"pl": "(brak pozycji w rejestrze)", "en": "(missing from registry)"},

    # ----- path -----
    "kb.path.usage": {
        "pl": "Użycie: kb path <topic_id>. Generuje ścieżkę od łatwych do trudnych.",
        "en": "Usage: kb path <topic_id>. Builds an easy-to-hard path.",
    },
    "kb.path.unknown_topic": {
        "pl": "Nieznany temat: {topic}.",
        "en": "Unknown topic: {topic}.",
    },
    "kb.path.title": {
        "pl": "Ścieżka czytelnicza: {topic}",
        "en": "Reading path: {topic}",
    },
    "kb.path.empty": {
        "pl": "Temat nie ma jeszcze pozycji do uszeregowania.",
        "en": "No resources to order for this topic yet.",
    },

    # ----- stats -----
    "kb.stats.title": {
        "pl": "Statystyki bazy wiedzy",
        "en": "Knowledge base statistics",
    },
    "kb.stats.totals": {
        "pl": "Tematy: {topics}   Pozycje: {resources}   Ścieżki: {bundles}",
        "en": "Topics: {topics}   Resources: {resources}   Bundles: {bundles}",
    },
    "kb.stats.by_kind":       {"pl": "Wg rodzaju", "en": "By kind"},
    "kb.stats.by_topic":      {"pl": "Wg tematu", "en": "By topic"},
    "kb.stats.by_difficulty": {"pl": "Wg trudności", "en": "By difficulty"},
    "kb.stats.by_license":    {"pl": "Wg licencji", "en": "By license"},

    # ----- dispatcher / errors -----
    "kb.unknown_sub": {
        "pl": "Nieznana podkomenda: {sub}.",
        "en": "Unknown subcommand: {sub}.",
    },
    "kb.unknown_sub_hint": {
        "pl": "Wpisz `help kb` po pełną listę podkomend.",
        "en": "Type `help kb` for the full subcommand list.",
    },
    "kb.argparse_err": {
        "pl": "Błąd parsowania argumentów: {error}",
        "en": "Argument parsing error: {error}",
    },
    "kb.bad_difficulty": {
        "pl": "Niepoprawny zakres trudności: {value}. Użyj formatu `1-3` albo pojedynczej liczby.",
        "en": "Invalid difficulty range: {value}. Use `1-3` or a single integer.",
    },

    # ----- cross-reference (used by other commands) -----
    "kb.crossref.combinators": {
        "pl": "Powiązane KB: `kb topic combinators`",
        "en": "Related KB: `kb topic combinators`",
    },
    "kb.crossref.curry_howard": {
        "pl": "Powiązane KB: `kb topic curry-howard`",
        "en": "Related KB: `kb topic curry-howard`",
    },
    "kb.crossref.propositional_logic": {
        "pl": "Powiązane KB: `kb topic propositional-logic`",
        "en": "Related KB: `kb topic propositional-logic`",
    },
    "kb.crossref.aristotle": {
        "pl": "Powiązane KB: `kb topic aristotle-system`",
        "en": "Related KB: `kb topic aristotle-system`",
    },

    # ----- long help -----
    "help.long.kb": {
        "pl": (
            "kb — przeglądarka skuratowanej literatury (~120 pozycji w 16 tematach,\n"
            "7 ścieżek czytelniczych).\n\n"
            "Podkomendy:\n"
            "  kb                        — panel powitalny + skróty.\n"
            "  kb topics                 — tabela wszystkich tematów + liczba pozycji.\n"
            "  kb topic <id>             — intro tematu + lista lektur (kanon na górze).\n"
            "                              Filtry: --difficulty 1-3, --kind paper,book\n"
            "  kb show <id>              — pełny panel pozycji (autorzy, abstrakt, dlaczego,\n"
            "                              URL/DOI/arXiv/ISBN). Po wydruku pyta czy otworzyć.\n"
            "                              `--no-open` pomija prompt.\n"
            "  kb open <id>              — od razu otwiera URL/PDF w domyślnej aplikacji.\n"
            "  kb search <słowo>         — szuka po tytule/autorach/abstrakcie/tagach.\n"
            "                              Filtry: --topic <id>, --kind k, --difficulty d.\n"
            "  kb random                 — losowa pozycja (możesz dodać --topic <id>).\n"
            "  kb bundles                — lista ścieżek czytelniczych.\n"
            "  kb bundle <id>            — szczegóły ścieżki + uporządkowana lista.\n"
            "  kb path <topic_id>        — automatyczna ścieżka: kanon + reszta wg trudności.\n"
            "  kb stats                  — liczby wg rodzaju / tematu / trudności / licencji.\n\n"
            "Przykłady:\n"
            "  kb topic combinators\n"
            "  kb topic inductive-types --difficulty 1-3\n"
            "  kb show pierce-tapl\n"
            "  kb search Curry-Howard --kind paper\n"
            "  kb bundle ai-mathematics-2024-2026\n"
        ),
        "en": (
            "kb -- a curated literature browser (~120 entries across 16 topics,\n"
            "7 reading bundles).\n\n"
            "Subcommands:\n"
            "  kb                        -- welcome panel + shortcuts.\n"
            "  kb topics                 -- table of every topic with resource counts.\n"
            "  kb topic <id>             -- topic intro + reading list (canon on top).\n"
            "                              Filters: --difficulty 1-3, --kind paper,book\n"
            "  kb show <id>              -- full resource panel (authors, abstract, why,\n"
            "                              URL/DOI/arXiv/ISBN). Asks before opening.\n"
            "                              Use `--no-open` to skip the prompt.\n"
            "  kb open <id>              -- open URL/PDF in the default app immediately.\n"
            "  kb search <keyword>       -- searches title / authors / abstracts / tags.\n"
            "                              Filters: --topic <id>, --kind k, --difficulty d.\n"
            "  kb random                 -- random recommendation (add --topic <id>).\n"
            "  kb bundles                -- list curated reading bundles.\n"
            "  kb bundle <id>            -- bundle details + ordered reading list.\n"
            "  kb path <topic_id>        -- auto path: canon + rest sorted by difficulty.\n"
            "  kb stats                  -- counts by kind / topic / difficulty / license.\n\n"
            "Examples:\n"
            "  kb topic combinators\n"
            "  kb topic inductive-types --difficulty 1-3\n"
            "  kb show pierce-tapl\n"
            "  kb search Curry-Howard --kind paper\n"
            "  kb bundle ai-mathematics-2024-2026\n"
        ),
    },

    # =====================================================================
    # === Lean Games (PLAN_GAMES.md) — added in Phase 5; keep at the END ==
    # === so the structural-sync agent's edits land cleanly above this. ===
    # =====================================================================

    "cmd.games": {
        "pl": "interaktywne gry Lean (port NNG4): swiat → poziom → dowod",
        "en": "interactive Lean games (NNG4 port): world → level → proof",
    },

    # ----- list / overview -----
    "games.help.title": {
        "pl": "games — interaktywne gry Lean",
        "en": "games — interactive Lean games",
    },
    "games.help.body": {
        "pl": (
            "Komendy:\n"
            "  games                          — lista dostepnych gier\n"
            "  games <game>                   — swiaty gry\n"
            "  games <game> <world>           — poziomy swiata\n"
            "  games play <game> <world> <n>  — graj poziom n\n"
            "  games session [<game>]         — tryb sesji (auto-pickuje nastepny, ENTER = dalej)\n"
            "  games next [<game>]            — otworz nastepny nieukonczony\n"
            "  games progress [<game>]        — postepy\n\n"
            "Wewnatrz poziomu:\n"
            "  ENTER — sprawdz wpisany kod Lean\n"
            "  h     — podpowiedz LLM (kazde nacisniecie eskaluje: 1 nudge → 2 direct → 3 spell-it-out)\n"
            "  t     — sciaga: skladnia + przyklady aktualnie dostepnych taktyk\n"
            "  m     — pokaz model_solution (liczy sie jako skip)\n"
            "  s     — skip\n"
            "  q     — wyjdz\n"
            "  ?     — pokaz naglowek poziomu jeszcze raz\n"
        ),
        "en": (
            "Commands:\n"
            "  games                          — list available games\n"
            "  games <game>                   — worlds of a game\n"
            "  games <game> <world>           — levels of a world\n"
            "  games play <game> <world> <n>  — play level n\n"
            "  games session [<game>]         — session mode (auto-picks next, ENTER = continue)\n"
            "  games next [<game>]            — open the next unsolved level\n"
            "  games progress [<game>]        — progress per world\n\n"
            "Inside a level:\n"
            "  ENTER — submit the Lean tactic block you typed\n"
            "  h     — LLM hint (each press escalates: 1 nudge → 2 direct → 3 spell-it-out)\n"
            "  t     — cheat sheet: syntax + examples for the available tactics\n"
            "  m     — show the model solution (counts as skipped)\n"
            "  s     — skip\n"
            "  q     — quit\n"
            "  ?     — re-show the level header\n"
        ),
    },
    "games.no_games": {
        "pl": "Brak gier w lambda_lab/lab/games/data/.",
        "en": "No games found under lambda_lab/lab/games/data/.",
    },
    "games.warnings_header": {
        "pl": "({count} ostrzezen przy ladowaniu — patrz dziennik.)",
        "en": "({count} loader warning(s) — see the journal.)",
    },
    "games.unknown_game": {
        "pl": "Nie znam gry: {game}. Wpisz `games`, by zobaczyc liste.",
        "en": "Unknown game: {game}. Type `games` to see the list.",
    },
    "games.unknown_world": {
        "pl": "Gra {game} nie ma swiata {world}.",
        "en": "Game {game} has no world named {world}.",
    },
    "games.parse_err": {
        "pl": "Blad parsowania argumentow: {error}",
        "en": "Argument parsing error: {error}",
    },

    # ----- table headers -----
    "games.list.title": {"pl": "Dostepne gry", "en": "Available games"},
    "games.list.col.id": {"pl": "id", "en": "id"},
    "games.list.col.title": {"pl": "Tytul", "en": "Title"},
    "games.list.col.worlds": {"pl": "Swiaty", "en": "Worlds"},
    "games.list.col.description": {"pl": "Opis", "en": "Description"},
    "games.list.hint": {
        "pl": "Wpisz `games <id>` aby zobaczyc swiaty.",
        "en": "Type `games <id>` to see worlds.",
    },

    "games.worlds.title": {"pl": "Swiaty: {game}", "en": "Worlds: {game}"},
    "games.worlds.col.id": {"pl": "id", "en": "id"},
    "games.worlds.col.title": {"pl": "Tytul", "en": "Title"},
    "games.worlds.col.levels": {"pl": "Poziomy", "en": "Levels"},
    "games.worlds.col.intro": {"pl": "Wstep", "en": "Intro"},
    "games.worlds.hint": {
        "pl": "Wpisz `games {game} <world>` aby zobaczyc poziomy.",
        "en": "Type `games {game} <world>` to see levels.",
    },

    "games.levels.title": {"pl": "Poziomy: {game} / {world}", "en": "Levels: {game} / {world}"},
    "games.levels.col.title": {"pl": "Tytul", "en": "Title"},
    "games.levels.col.diff": {"pl": "Trud.", "en": "Diff."},
    "games.levels.col.statement": {"pl": "Tresc", "en": "Statement"},
    "games.levels.col.status": {"pl": "Status", "en": "Status"},
    "games.levels.status.todo": {"pl": "do zrobienia", "en": "todo"},
    "games.levels.status.solved": {"pl": "rozwiazane", "en": "solved"},
    "games.levels.status.skipped": {"pl": "pominiete", "en": "skipped"},
    "games.levels.hint": {
        "pl": "Wpisz `games play {game} {world} <n>` aby zagrac poziom.",
        "en": "Type `games play {game} {world} <n>` to play a level.",
    },

    # ----- play / runner -----
    "games.play.usage": {
        "pl": "Uzycie: games play <game> <world> <level_no>",
        "en": "Usage: games play <game> <world> <level_no>",
    },
    "games.play.bad_level": {
        "pl": "Nieprawidlowy numer poziomu: {token}",
        "en": "Invalid level number: {token}",
    },
    "games.play.no_level": {
        "pl": "Gra {game} swiat {world} nie ma poziomu nr {level}.",
        "en": "Game {game} world {world} has no level #{level}.",
    },

    "games.runner.header_line": {
        "pl": "{game} - {world} - poziom {level}/{total}",
        "en": "{game} - {world} - level {level}/{total}",
    },
    "games.runner.intro_label": {"pl": "Wstep", "en": "Intro"},
    "games.runner.statement_label": {"pl": "Cel", "en": "Goal"},
    "games.runner.tactics_label": {"pl": "Dostepne taktyki", "en": "Available tactics"},
    "games.runner.goal_title": {"pl": "Lean — cel", "en": "Lean — goal"},
    "games.runner.controls_hint": {
        "pl": "Wpisz dowod (lub h/m/s/q/?). ENTER wysyla.",
        "en": "Type your proof (or h/m/s/q/?). ENTER submits.",
    },
    "games.runner.prompt": {"pl": "[level]> ", "en": "[level]> "},
    "games.runner.failed_title": {"pl": "Lean odrzucil dowod", "en": "Lean rejected the proof"},
    "games.runner.attempt_failed_intro": {
        "pl": "Sproba: {attempt}",
        "en": "Attempt: {attempt}",
    },
    "games.runner.no_diags": {
        "pl": "(Brak diagnostyki — pewnie literowka.)",
        "en": "(No diagnostics — probably a typo.)",
    },
    "games.runner.failed_hint": {
        "pl": "Sprobuj jeszcze raz, h = podpowiedz, m = model, s = skip, q = wyjdz.",
        "en": "Try again, h = hint, m = model, s = skip, q = quit.",
    },
    "games.runner.solved_title": {
        "pl": "ROZWIAZANE — poziom {level}",
        "en": "SOLVED — level {level}",
    },
    "games.runner.attempts_label": {"pl": "Proby", "en": "Attempts"},
    "games.runner.hints_label": {"pl": "Uzyte podpowiedzi", "en": "Hints used"},
    "games.runner.duration_label": {"pl": "Czas", "en": "Duration"},
    "games.runner.model_title": {"pl": "Model solution", "en": "Model solution"},
    "games.runner.model_counts_skipped": {
        "pl": "(To liczy sie jako pominiete w postepach.)",
        "en": "(This counts as skipped in your progress.)",
    },
    "games.runner.skipped": {
        "pl": "Poziom pominiety.",
        "en": "Level skipped.",
    },
    "games.runner.hint_requesting": {
        "pl": "Pytam LLM o podpowiedz (tier {tier})...",
        "en": "Asking the LLM for a hint (tier {tier})...",
    },
    "games.runner.hint_title": {
        "pl": "Podpowiedz (tier {tier})",
        "en": "Hint (tier {tier})",
    },
    "games.runner.hint_unavailable_title": {
        "pl": "Podpowiedz niedostepna",
        "en": "Hint unavailable",
    },
    "games.runner.hint_unavailable_body": {
        "pl": (
            "Brak klucza OpenAI lub problem z siecia. "
            "Skonfiguruj ~/.config/openai/env i ustaw OPENAI_API_KEY, "
            "albo wpisz `m` zeby zobaczyc model_solution."
        ),
        "en": (
            "No OpenAI API key or a network problem. "
            "Configure ~/.config/openai/env with OPENAI_API_KEY, "
            "or type `m` to see the model solution."
        ),
    },
    "games.runner.lake_missing": {
        "pl": "Brak `lake` w PATH — zainstaluj elan/Lean.",
        "en": "`lake` is not in PATH — install elan/Lean.",
    },
    "games.runner.no_lake_project": {
        "pl": "Brak projektu Lake (lambda_lab/proofs/lean_aristotle).",
        "en": "Missing Lake project (lambda_lab/proofs/lean_aristotle).",
    },
    "games.runner.verify_error": {
        "pl": "Blad weryfikatora: {error}",
        "en": "Verifier error: {error}",
    },

    # ----- next / progress -----
    "games.next.opening": {
        "pl": "Otwieram nastepny: {game}/{world}/{level}.",
        "en": "Opening the next level: {game}/{world}/{level}.",
    },
    "games.next.all_done": {
        "pl": "Wszystkie poziomy {game} rozwiazane. Gratulacje!",
        "en": "All levels of {game} are solved. Congratulations!",
    },

    "games.progress.title": {"pl": "Postepy: {game}", "en": "Progress: {game}"},
    "games.progress.col.world": {"pl": "Swiat", "en": "World"},
    "games.progress.col.solved": {"pl": "rozwiazane", "en": "solved"},
    "games.progress.col.skipped": {"pl": "pominiete", "en": "skipped"},
    "games.progress.col.todo": {"pl": "do zrobienia", "en": "todo"},
    "games.progress.col.ratio": {"pl": "stosunek", "en": "ratio"},

    # ----- session mode -----
    "games.session.welcome_title": {
        "pl": "Tryb sesji: {game}",
        "en": "Session mode: {game}",
    },
    "games.session.welcome_body": {
        "pl": (
            "Po kazdym ukonczonym poziomie nacisnij ENTER, aby przejsc dalej; "
            "wpisz `q` aby wyjsc. Wewnatrz poziomu uzyj `t` aby zobaczyc skladnie "
            "i przyklady dostepnych taktyk."
        ),
        "en": (
            "Press ENTER after each finished level to advance; type `q` to leave. "
            "Inside a level, press `t` to expand syntax and examples for the "
            "currently available tactics."
        ),
    },
    "games.session.prewarming": {
        "pl": "Rozgrzewam serwer Lean (Mathlib v4.28)...",
        "en": "Warming up the Lean server (Mathlib v4.28)...",
    },
    "games.session.server_already_warm": {
        "pl": "Serwer Lean juz dziala -- kompilacje beda szybkie.",
        "en": "Lean server is already alive -- compilations will be fast.",
    },
    "games.session.prewarm_failed": {
        "pl": "Nie udalo sie rozgrzac serwera Lean ({error}); uzyje trybu inline.",
        "en": "Could not warm up the Lean server ({error}); falling back to inline.",
    },
    "games.session.warming_tactics": {
        "pl": "Rozgrzewam taktyki (ring/linarith/omega/simp/norm_num) — pierwszy raz ~20 s, kolejne poziomy beda szybkie.",
        "en": "Warming tactic caches (ring/linarith/omega/simp/norm_num) — first time ~20 s, subsequent levels will be fast.",
    },
    "games.session.warm_tactics_failed": {
        "pl": "Nie rozgrzano taktyk ({error}); pierwsza ciezka taktyka moze byc wolna.",
        "en": "Could not warm tactic caches ({error}); the first heavy tactic may be slow.",
    },
    "games.runner.tactics_ref.lemma_label": {
        "pl": "Mathlib lemmat: {statement}",
        "en": "Mathlib lemma: {statement}",
    },
    "games.runner.tactics_ref.lemma_unknown": {
        "pl": "Mathlib lemmat (brak w sciagi)",
        "en": "Mathlib lemma (not in cheat sheet)",
    },
    "games.runner.tactics_ref.lemma_usage_hint": {
        "pl": "Uzyj: exact {name} ...  /  rw [{name}]",
        "en": "Use: exact {name} ...  /  rw [{name}]",
    },
    "games.session.continue_prompt": {
        "pl": "ENTER aby przejsc do nastepnego poziomu, q aby wyjsc: ",
        "en": "Press ENTER for the next level, q to quit: ",
    },
    "games.session.bye": {
        "pl": "Do zobaczenia w kolejnej sesji!",
        "en": "See you in the next session!",
    },
    "games.session.all_done": {
        "pl": "Wszystkie poziomy {game} ukonczone!",
        "en": "All levels of {game} finished!",
    },

    # ----- runner: tactics reference (`t` key) -----
    "games.runner.tactics_ref.title": {
        "pl": "Sciaga: skladnia dostepnych taktyk",
        "en": "Cheat sheet: syntax of available tactics",
    },
    "games.runner.tactics_ref.empty": {
        "pl": "Ten poziom nie deklaruje listy dostepnych taktyk.",
        "en": "This level does not declare a list of available tactics.",
    },
    "games.runner.tactics_ref.no_doc": {
        "pl": "(brak opisu w encyklopedii)",
        "en": "(no encyclopedia entry)",
    },
    "games.runner.tactics_ref.col.name":   {"pl": "Taktyka",   "en": "Tactic"},
    "games.runner.tactics_ref.col.what":   {"pl": "Co robi",   "en": "What it does"},
    "games.runner.tactics_ref.col.before": {"pl": "Przyklad cel", "en": "Example goal"},
    "games.runner.tactics_ref.col.after":  {"pl": "Po taktyce",   "en": "After tactic"},

    # ----- long help (registered via help.py LONG_HELP_KEYS) -----
    "help.long.games": {
        "pl": (
            "games -- terminalowy port NNG4 (Natural Number Game).\n\n"
            "Subkomendy:\n"
            "  games                            -- lista gier (w MVP: nng4).\n"
            "  games <game>                     -- swiaty gry (Tutorial / Dodawanie / Mnozenie).\n"
            "  games <game> <world>             -- poziomy z trudnoscia i statusem.\n"
            "  games play <game> <world> <n>    -- interaktywny runner (REPL w REPL).\n"
            "  games next [<game>]              -- pierwszy nieukonczony poziom.\n"
            "  games progress [<game>]          -- ratio rozwiazane/pominiete/todo per swiat.\n\n"
            "Wewnatrz poziomu wpisujesz kod Lean (cialo dowodu — to co stoi po `:= by`).\n"
            "Twoj kod sklejamy z preambula i zdaniem poziomu, zapisujemy w\n"
            "lambda_lab/proofs/lean_aristotle/LambdaAristotle/Games/<game>/<world>/<level>.lean,\n"
            "i wysylamy do persystentnego LSP (LeanServer.get) — taki sam, ktorego uzywa\n"
            "`ch verify` i `arist compile --server`. Mathlib lubi sie wczytac raz na sesje.\n\n"
            "Specjalne klawisze w interaktywnym runnerze:\n"
            "  ENTER       -- wyslij kod do Lean\n"
            "  h           -- podpowiedz (LLM, eskaluje 1->2->3)\n"
            "  m           -- pokaz model_solution (liczy sie jako skip)\n"
            "  s           -- skip (nie liczy sie jako rozwiazane)\n"
            "  q           -- wyjdz bez zapisu\n"
            "  ?           -- pokaz naglowek poziomu jeszcze raz\n\n"
            "Postepy zapisuja sie w ~/.local/share/lambda_lab/games_progress.jsonl\n"
            "(jeden JSON na linie — przezywa restart REPL-a).\n\n"
            "Atrybucje: NNG4 (Apache-2.0), Kevin Buzzard, Mohammad Pedramfar et al.\n"
            "Tresc poziomow zaadaptowana do Lean 4.28 + Mathlib 4.28.\n\n"
            "Przyklady:\n"
            "  games\n"
            "  games nng4\n"
            "  games nng4 tutorial\n"
            "  games play nng4 tutorial 1\n"
            "  games progress\n"
        ),
        "en": (
            "games -- a terminal port of NNG4 (Natural Number Game).\n\n"
            "Subcommands:\n"
            "  games                            -- list games (MVP: nng4).\n"
            "  games <game>                     -- worlds of a game (Tutorial / Addition / Multiplication).\n"
            "  games <game> <world>             -- levels with difficulty and status.\n"
            "  games play <game> <world> <n>    -- interactive runner (REPL inside REPL).\n"
            "  games next [<game>]              -- the first unsolved level.\n"
            "  games progress [<game>]          -- solved/skipped/todo ratio per world.\n\n"
            "Inside a level you type Lean code (the proof body — what comes after `:= by`).\n"
            "Your code is concatenated with the level preamble and statement, written to\n"
            "lambda_lab/proofs/lean_aristotle/LambdaAristotle/Games/<game>/<world>/<level>.lean,\n"
            "and sent to the persistent LSP (LeanServer.get) — the very same one used by\n"
            "`ch verify` and `arist compile --server`. Mathlib loads once per session.\n\n"
            "Special inputs in the interactive runner:\n"
            "  ENTER       -- submit the Lean code\n"
            "  h           -- hint (LLM, escalates 1->2->3)\n"
            "  m           -- show model_solution (counts as a skip)\n"
            "  s           -- skip (does NOT count as solved)\n"
            "  q           -- quit without recording\n"
            "  ?           -- re-show the level header\n\n"
            "Progress is persisted in ~/.local/share/lambda_lab/games_progress.jsonl\n"
            "(one JSON per line — survives REPL restarts).\n\n"
            "Credits: NNG4 (Apache-2.0), Kevin Buzzard, Mohammad Pedramfar et al.\n"
            "Level content adapted to Lean 4.28 + Mathlib 4.28.\n\n"
            "Examples:\n"
            "  games\n"
            "  games nng4\n"
            "  games nng4 tutorial\n"
            "  games play nng4 tutorial 1\n"
            "  games progress\n"
        ),
    },

    # ============================================================
    # ch explore — interactive walker over Lean proof terms
    # ============================================================
    "ch.explore.usage": {
        "pl": (
            "Uzycie: ch explore [slug]  (katalog)  |  "
            "ch explore --live --src '<lean source>' [--name N] [--no-walker]  (na zywo)."
        ),
        "en": (
            "Usage: ch explore [slug]  (catalogue)  |  "
            "ch explore --live --src '<lean source>' [--name N] [--no-walker]  (live)."
        ),
    },
    "ch.explore.unknown_slug": {
        "pl": "Nie znam pozycji `{slug}`. Wpisz `ch explore` aby zobaczyc katalog.",
        "en": "Unknown entry `{slug}`. Type `ch explore` to see the catalogue.",
    },
    "ch.explore.empty_catalog": {
        "pl": "Katalog ch explore jest pusty.",
        "en": "The ch explore catalogue is empty.",
    },
    "ch.explore.list_title": {
        "pl": "Katalog ch explore",
        "en": "ch explore catalogue",
    },
    "ch.explore.col.slug": {"pl": "Slug", "en": "Slug"},
    "ch.explore.col.title": {"pl": "Tytul", "en": "Title"},
    "ch.explore.col.type": {"pl": "Typ", "en": "Type"},
    "ch.explore.col.diff": {"pl": "Trud.", "en": "Diff."},
    "ch.explore.col.line": {"pl": "L", "en": "L"},
    "ch.explore.col.tactic": {"pl": "Taktyka", "en": "Tactic"},
    "ch.explore.col.path": {"pl": "Sciezka", "en": "Path"},
    "ch.explore.col.narrative": {"pl": "Co robi", "en": "What it does"},
    "ch.explore.no_tactics": {
        "pl": "Brak krokow taktycznych w tej pozycji.",
        "en": "No tactic steps for this entry.",
    },
    "ch.explore.mapping_title": {
        "pl": "Mapowanie taktyka -> podterm",
        "en": "Tactic -> subterm mapping",
    },
    "ch.explore.lambda_title": {
        "pl": "Czysty lambda-rownowaznik",
        "en": "Pure lambda equivalent",
    },
    "ch.explore.tree_title": {
        "pl": "Term dowodu",
        "en": "Proof term",
    },
    "ch.explore.overview_title": {
        "pl": "ch explore - {slug}",
        "en": "ch explore - {slug}",
    },
    "ch.explore.row.id": {"pl": "Id", "en": "Id"},
    "ch.explore.row.title": {"pl": "Tytul", "en": "Title"},
    "ch.explore.row.difficulty": {"pl": "Trudnosc", "en": "Difficulty"},
    "ch.explore.row.type": {"pl": "Typ", "en": "Type"},
    "ch.explore.row.summary": {"pl": "Streszczenie", "en": "Summary"},
    "ch.explore.row.lean_source": {
        "pl": "Zrodlo Lean (taktyczne)",
        "en": "Lean source (tactic)",
    },
    "ch.explore.collapsed_marker": {
        "pl": "[zwiniete]",
        "en": "[collapsed]",
    },
    "ch.explore.controls_hint": {
        "pl": "Sterowanie: <numer> zwin/rozwin, t typy, i implicit, l lambda, m widok mat., a abstract, n narracja, p parafraza LLM, next/prev nawigacja, ? overview, q wyjscie.",
        "en": "Controls: <number> toggle node, t types, i implicit, l lambda, m math view, a abstract, n narrative, p LLM paraphrase, next/prev navigation, ? overview, q quit.",
    },
    "ch.explore.prompt": {
        "pl": "explore> ",
        "en": "explore> ",
    },
    "ch.explore.bye": {
        "pl": "Wychodzimy z ch explore.",
        "en": "Leaving ch explore.",
    },
    "ch.explore.toggle_node": {
        "pl": "Wezel {idx}: {state}.",
        "en": "Node {idx}: {state}.",
    },
    "ch.explore.state.collapsed": {"pl": "zwiniety", "en": "collapsed"},
    "ch.explore.state.expanded": {"pl": "rozwiniety", "en": "expanded"},
    "ch.explore.toggle_types": {
        "pl": "Adnotacje typow: {state}.",
        "en": "Type annotations: {state}.",
    },
    "ch.explore.toggle_implicits": {
        "pl": "Argumenty implicit: {state}.",
        "en": "Implicit arguments: {state}.",
    },
    "ch.explore.toggle_lambda": {
        "pl": "Panel lambda: {state}.",
        "en": "Lambda panel: {state}.",
    },
    "ch.explore.toggle_math": {
        "pl": "Widok matematyczny: {state}.",
        "en": "Math view: {state}.",
    },
    "ch.explore.toggle_narrative": {
        "pl": "Parafraza narracyjna: {state}.",
        "en": "Narrative paraphrase: {state}.",
    },
    "ch.explore.toggle_abstract": {
        "pl": "Widok abstrakcyjny: {state}.",
        "en": "Abstract view: {state}.",
    },
    "ch.explore.abstract.title": {
        "pl": "Widok abstrakcyjny",
        "en": "Abstract view",
    },
    "ch.explore.abstract.collapsed_title": {
        "pl": "Bloki taktyk zwiniete",
        "en": "Tactic blocks collapsed",
    },
    "ch.explore.abstract.collapsed_row": {
        "pl": "  {label} - {count} podtermow",
        "en": "  {label} - {count} subterms",
    },
    "ch.explore.state.on": {"pl": "wlaczone", "en": "on"},
    "ch.explore.state.off": {"pl": "wylaczone", "en": "off"},
    "ch.explore.unknown_node": {
        "pl": "Brak wezla o numerze {idx} (zakres: 0..{max}).",
        "en": "No node with index {idx} (range: 0..{max}).",
    },
    "ch.explore.unknown_input": {
        "pl": "Nieznana komenda. Wpisz `?` aby zobaczyc skroty albo `q` aby wyjsc.",
        "en": "Unknown input. Type `?` for shortcuts or `q` to quit.",
    },
    "ch.explore.next_unavailable": {
        "pl": "To ostatnia pozycja w katalogu.",
        "en": "This is the last entry in the catalogue.",
    },
    "ch.explore.prev_unavailable": {
        "pl": "To pierwsza pozycja w katalogu.",
        "en": "This is the first entry in the catalogue.",
    },
    "ch.explore.entering": {
        "pl": "Wchodzimy w pozycje [brand]{slug}[/brand].",
        "en": "Entering entry [brand]{slug}[/brand].",
    },
    # ----- raw / unparsed marker (rendered next to nodes that fell back) ----
    "ch.explore.raw_marker": {
        "pl": "(nierozpoznane)",
        "en": "(unparsed)",
    },
    # ----- live mode (--live) ----------------------------------------------
    "ch.explore.live.usage": {
        "pl": (
            "Uzycie: ch explore --live --src '<lean source>'  lub  "
            "ch explore --live --file <sciezka>. Opcjonalnie --name <ident>, --no-walker, --paraphrase."
        ),
        "en": (
            "Usage: ch explore --live --src '<lean source>'  or  "
            "ch explore --live --file <path>. Optional --name <ident>, --no-walker, --paraphrase."
        ),
    },
    "ch.explore.live.compiling": {
        "pl": "Kompiluje zrodlo Lean i pobieram term dowodu...",
        "en": "Compiling Lean source and fetching the proof term...",
    },
    "ch.explore.live.parsing": {
        "pl": "Parsuje term dowodu do drzewa AST...",
        "en": "Parsing the proof term into an AST...",
    },
    "ch.explore.live.no_name": {
        "pl": (
            "Nie znalazlem nazwy twierdzenia w zrodle. Dopisz `theorem nazwa ...` "
            "albo podaj `--name nazwa`."
        ),
        "en": (
            "Could not find a theorem name in the source. Add `theorem name ...` "
            "or pass `--name name`."
        ),
    },
    "ch.explore.live.compile_failed": {
        "pl": "Lean odrzucil zrodlo. Pelne wyjscie ponizej.",
        "en": "Lean rejected the source. Full output below.",
    },
    "ch.explore.live.no_print_output": {
        "pl": (
            "Lean nie wypisal `#print <name>` (brak termu dowodu). "
            "Sprawdz, czy nazwa twierdzenia sie zgadza."
        ),
        "en": (
            "Lean did not emit `#print <name>` (no proof term). "
            "Check that the theorem name matches."
        ),
    },
    "ch.explore.live.parse_failed": {
        "pl": "Nie udalo sie sparsowac termu (pokazuje go jako `raw`)",
        "en": "Failed to parse the proof term (showing it as `raw`)",
    },
    "ch.explore.live.summary": {
        "pl": "Term dowodu pobrany na zywo z Leana.",
        "en": "Proof term fetched live from Lean.",
    },
    "ch.explore.live.title": {
        "pl": "ch explore --live - blad",
        "en": "ch explore --live - error",
    },
    "ch.explore.live.lake_missing": {
        "pl": (
            "Brak `lake` w PATH (Lean toolchain). Zainstaluj elan/lake, "
            "albo uzyj `arist server start`."
        ),
        "en": (
            "`lake` is not in PATH (Lean toolchain). Install elan/lake, "
            "or use `arist server start`."
        ),
    },
    "ch.explore.live.help_hint": {
        "pl": "Wpisz `help ch` aby zobaczyc pelne uzycie `ch explore --live`.",
        "en": "Type `help ch` to see the full usage of `ch explore --live`.",
    },
    "ch.explore.live.success_banner": {
        "pl": "Term `{name}` pobrany i sparsowany.",
        "en": "Term `{name}` fetched and parsed.",
    },

    # -----------------------------------------------------------------------
    # Tutorial subsystem (multi-chapter walkthrough)
    # -----------------------------------------------------------------------
    "cmd.tutorial": {
        "pl": "tutorial dydaktyczny: 6 rozdzialow z dowodami klasycznych twierdzen w Lean",
        "en": "guided tutorial: 6 chapters proving classical theorems in Lean",
    },
    "tutorial.help.title": {
        "pl": "Tutorial - pomoc",
        "en": "Tutorial - help",
    },
    "tutorial.help.body": {
        "pl": (
            "Komenda `tutorial` to spojny przewodnik po szesciu rozdzialach matematyki:\n"
            "  tutorial                    - wyswietl tabele rozdzialow\n"
            "  tutorial <slug|numer>       - uruchom rozdzial (np. `tutorial 1` lub `tutorial gauss_sum`)\n"
            "  tutorial next               - automatycznie przejdz do nastepnego nieukonczonego\n"
            "  tutorial progress           - tabela statusow\n"
            "  tutorial reset              - wyczysc dziennik postepow\n"
            "  tutorial help               - pokaz te pomoc\n\n"
            "W trakcie rozdzialu: ENTER = dalej, s = pomin krok, q = wyjdz, ? = pokaz krok ponownie."
        ),
        "en": (
            "The `tutorial` command is a coherent walk through six mathematical chapters:\n"
            "  tutorial                    - print the table of chapters\n"
            "  tutorial <slug|number>      - run a chapter (e.g. `tutorial 1` or `tutorial gauss_sum`)\n"
            "  tutorial next               - jump to the next unfinished chapter\n"
            "  tutorial progress           - status table\n"
            "  tutorial reset              - clear the progress journal\n"
            "  tutorial help               - show this help\n\n"
            "During a chapter: ENTER = advance, s = skip the step, q = quit, ? = re-show the step."
        ),
    },
    "tutorial.table.title": {
        "pl": "Tutorial Lambda Lab - rozdzialy",
        "en": "Lambda Lab tutorial - chapters",
    },
    "tutorial.table.col.idx": {"pl": "#", "en": "#"},
    "tutorial.table.col.title": {"pl": "Rozdzial", "en": "Chapter"},
    "tutorial.table.col.steps": {"pl": "Kroki", "en": "Steps"},
    "tutorial.table.col.duration": {"pl": "Czas", "en": "Time"},
    "tutorial.table.col.status": {"pl": "Status", "en": "Status"},
    "tutorial.table.hint": {
        "pl": "Wpisz `tutorial 1`, `tutorial <slug>` albo `tutorial next`.",
        "en": "Type `tutorial 1`, `tutorial <slug>` or `tutorial next`.",
    },
    "tutorial.status.not_started": {"pl": "nie zaczety", "en": "not started"},
    "tutorial.status.in_progress": {"pl": "w toku", "en": "in progress"},
    "tutorial.status.complete": {"pl": "ukonczony", "en": "complete"},
    "tutorial.kind.narrative": {"pl": "Narracja", "en": "Narrative"},
    "tutorial.kind.command": {"pl": "Komenda", "en": "Command"},
    "tutorial.kind.lean_walk": {"pl": "Spacer po termie Lean", "en": "Lean term walk"},
    "tutorial.kind.quiz_checkpoint": {"pl": "Checkpoint - quiz", "en": "Checkpoint - quiz"},
    "tutorial.kind.exercise": {"pl": "Cwiczenie", "en": "Exercise"},
    "tutorial.kind.kb": {"pl": "Lektura", "en": "Reading"},
    "tutorial.header.title": {
        "pl": "Rozdzial {n}: {name}",
        "en": "Chapter {n}: {name}",
    },
    "tutorial.header.meta": {
        "pl": "Krokow: {steps}, czas: ~{duration} min.",
        "en": "Steps: {steps}, time: ~{duration} min.",
    },
    "tutorial.header.controls": {
        "pl": "Sterowanie: ENTER = dalej, s = pomin krok, q = wyjdz, ? = pokaz krok ponownie.",
        "en": "Controls: ENTER = next, s = skip step, q = quit, ? = re-show step.",
    },
    "tutorial.step.title": {
        "pl": "Krok {idx}/{total}",
        "en": "Step {idx}/{total}",
    },
    "tutorial.step.controls_short": {
        "pl": "(ENTER = dalej · s = pomin · q = wyjdz · ? = pokaz ponownie)",
        "en": "(ENTER = next · s = skip · q = quit · ? = re-show)",
    },
    "tutorial.step.unknown_kind": {
        "pl": "Nieznany rodzaj kroku: {kind}.",
        "en": "Unknown step kind: {kind}.",
    },
    "tutorial.lean.source": {"pl": "Zrodlo Lean:", "en": "Lean source:"},
    "tutorial.lean.no_source": {
        "pl": "Brak zrodla Lean - krok pominiety.",
        "en": "No Lean source - step skipped.",
    },
    "tutorial.lean.skipped": {
        "pl": "Pomijam spacer po termie ({error}).",
        "en": "Skipping the term walk ({error}).",
    },
    "tutorial.lean.walker_failed": {
        "pl": "Walker termu zglosil blad: {error}.",
        "en": "Term walker reported an error: {error}.",
    },
    "tutorial.command.runs": {
        "pl": "Uruchamiam komende:",
        "en": "Running command:",
    },
    "tutorial.command.unknown": {
        "pl": "Nieznana komenda `{cmd}` - krok pominiety.",
        "en": "Unknown command `{cmd}` - step skipped.",
    },
    "tutorial.command.failed": {
        "pl": "Komenda `{cmd}` zglosila blad: {error}.",
        "en": "Command `{cmd}` reported an error: {error}.",
    },
    "tutorial.kb.opens": {
        "pl": "Po ENTER otworze `kb topic {topic}`.",
        "en": "On ENTER I will open `kb topic {topic}`.",
    },
    "tutorial.kb.failed": {
        "pl": "Nie udalo sie otworzyc tematu kb: {error}.",
        "en": "Failed to open the kb topic: {error}.",
    },
    "tutorial.quiz.bundle": {
        "pl": "Pakiet quizu: `{bundle}`.",
        "en": "Quiz bundle: `{bundle}`.",
    },
    "tutorial.quiz.threshold": {
        "pl": "Prog zaliczenia: {n} poprawnych.",
        "en": "Pass threshold: {n} correct answers.",
    },
    "tutorial.quiz.skipped": {
        "pl": "Quiz pominiety: {error}.",
        "en": "Quiz skipped: {error}.",
    },
    "tutorial.exercise.opens": {
        "pl": "Otwiera sie poziom cwiczeniowy w stylu `games play`.",
        "en": "Opening a `games play`-style exercise level.",
    },
    "tutorial.exercise.target": {
        "pl": "Cel: gra `{game}`, swiat `{world}`, poziom {level}.",
        "en": "Target: game `{game}`, world `{world}`, level {level}.",
    },
    "tutorial.exercise.no_spec": {
        "pl": "Brak specyfikacji cwiczenia w tym kroku.",
        "en": "No exercise spec attached to this step.",
    },
    "tutorial.exercise.not_found": {
        "pl": "Nie znalazlem poziomu {game}/{world}/{level}.",
        "en": "Could not find level {game}/{world}/{level}.",
    },
    "tutorial.exercise.lookup_failed": {
        "pl": "Wyszukiwanie poziomu nie powiodlo sie: {error}.",
        "en": "Level lookup failed: {error}.",
    },
    "tutorial.exercise.failed": {
        "pl": "Cwiczenie zglosilo blad: {error}.",
        "en": "Exercise reported an error: {error}.",
    },
    "tutorial.runner.prompt": {"pl": "[tutorial]> ", "en": "[tutorial]> "},
    "tutorial.runner.prompt_progress": {
        "pl": "[tutorial {step}/{total} — ENTER dalej, s pomin, q wyjdz, ? pokaz ponownie]> ",
        "en": "[tutorial {step}/{total} — ENTER next, s skip, q quit, ? re-show]> ",
    },
    "tutorial.runner.preaction_prompt": {
        "pl": "[ENTER aby uruchomic ten krok · s aby pominac · q aby wyjsc]> ",
        "en": "[ENTER to run this step · s to skip · q to quit]> ",
    },
    "tutorial.verbose.title": {
        "pl": "Uwaga: dluzszy fragment",
        "en": "Heads-up: long step",
    },
    "tutorial.verbose.body": {
        "pl": (
            "Ten krok wywoluje osadzony tryb (np. wycieczke albo walker), ktory wypisze "
            "wiele paneli - kazdy z wlasnym ENTER. Czytaj spokojnie. Jezeli nie chcesz "
            "ogladac, wpisz `s` zeby przeskoczyc."
        ),
        "en": (
            "This step embeds another mode (a tour, walker, or batch) that prints many "
            "panels with its own ENTER pacing. Take your time. Type `s` to skip if you "
            "don't want to watch the whole thing."
        ),
    },
    "tutorial.runner.controls_hint": {
        "pl": "ENTER = dalej, `s` = pomin, `q` = wyjdz, `?` = pokaz ponownie.",
        "en": "ENTER = advance, `s` = skip, `q` = quit, `?` = re-show.",
    },
    "tutorial.runner.skipped": {
        "pl": "Krok pominiety.",
        "en": "Step skipped.",
    },
    "tutorial.runner.bye": {
        "pl": "Wychodze z tutoriala. Postep zapisany.",
        "en": "Leaving the tutorial. Progress saved.",
    },
    "tutorial.complete.title": {
        "pl": "Rozdzial ukonczony",
        "en": "Chapter complete",
    },
    "tutorial.complete.body": {
        "pl": "Brawo - rozdzial `{name}` zaliczony. Wpisz `tutorial next` po nastepny.",
        "en": "Done - chapter `{name}` complete. Type `tutorial next` for the next one.",
    },
    "tutorial.progress.title": {
        "pl": "Postep w tutorialu",
        "en": "Tutorial progress",
    },
    "tutorial.progress.empty": {
        "pl": "Brak zapisanych prob. Zacznij od `tutorial 1`.",
        "en": "No recorded attempts. Start with `tutorial 1`.",
    },
    "tutorial.next.opening": {
        "pl": "Otwieram rozdzial {n}: {name}.",
        "en": "Opening chapter {n}: {name}.",
    },
    "tutorial.next.all_done": {
        "pl": "Wszystkie rozdzialy ukonczone. Gratulacje!",
        "en": "All chapters complete. Congratulations!",
    },
    "tutorial.unknown": {
        "pl": "Nie znam rozdzialu `{token}`. Wpisz `tutorial`, by zobaczyc liste.",
        "en": "I do not know chapter `{token}`. Type `tutorial` to see the list.",
    },
    "tutorial.empty_catalog": {
        "pl": "Katalog tutoriala jest pusty.",
        "en": "The tutorial catalog is empty.",
    },
    "tutorial.warnings_header": {
        "pl": "Ostrzezenia loadera ({count}):",
        "en": "Loader warnings ({count}):",
    },
    "tutorial.reset.ok": {
        "pl": "Dziennik postepu wyczyszczony.",
        "en": "Progress journal cleared.",
    },
    "tutorial.reset.fail": {
        "pl": "Nie udalo sie wyczyscic dziennika postepu.",
        "en": "Could not clear the progress journal.",
    },
    "help.long.tutorial": {
        "pl": (
            "Komenda `tutorial` to spojny przewodnik po szesciu klasycznych dowodach matematycznych\n"
            "zlozony z mieszanki narracji, spacerow po termach Lean, checkpointow quizowych i\n"
            "krotkich cwiczen w stylu Natural Number Game. Kazdy rozdzial ma zweryfikowane snippety\n"
            "Lean (kompiluja sie wzgledem Mathlib 4.28).\n\n"
            "Najwazniejsze podkomendy:\n"
            "  tutorial                    Tabela rozdzialow + status\n"
            "  tutorial 1                  Rozdzial 1 (Suma Gaussa)\n"
            "  tutorial gauss_sum          To samo co `tutorial 1`\n"
            "  tutorial next               Pierwszy nieukonczony rozdzial\n"
            "  tutorial progress           Krotka tabelka postepu\n"
            "  tutorial reset              Wyczysc dziennik\n"
            "  tutorial help               Pokaz te pomoc\n\n"
            "W srodku rozdzialu: ENTER (dalej), `s` (pomin), `q` (wyjdz), `?` (pokaz krok ponownie).\n"
            "Rozdzialy: 1) gauss_sum, 2) sqrt2_irrational, 3) pigeonhole, 4) infinitude_primes,\n"
            "5) am_gm_two, 6) heroic_finset_sum."
        ),
        "en": (
            "The `tutorial` command is a coherent walk through six classical mathematical proofs,\n"
            "blending narrative, Lean term walks, quiz checkpoints and short Natural-Number-Game-style\n"
            "exercises. Every Lean snippet is verified (compiles against Mathlib 4.28).\n\n"
            "Main sub-commands:\n"
            "  tutorial                    Table of chapters + status\n"
            "  tutorial 1                  Chapter 1 (Gauss's sum)\n"
            "  tutorial gauss_sum          Same as `tutorial 1`\n"
            "  tutorial next               First unfinished chapter\n"
            "  tutorial progress           Compact progress table\n"
            "  tutorial reset              Clear the journal\n"
            "  tutorial help               Show this help\n\n"
            "Inside a chapter: ENTER (advance), `s` (skip), `q` (quit), `?` (re-show step).\n"
            "Chapters: 1) gauss_sum, 2) sqrt2_irrational, 3) pigeonhole, 4) infinitude_primes,\n"
            "5) am_gm_two, 6) heroic_finset_sum."
        ),
    },

    # ============================================================
    # ch explore — math view + narrative paraphrase
    # ============================================================
    "ch.explore.math.title": {
        "pl": "Widok matematyczny",
        "en": "Math view",
    },
    "ch.explore.math.theorem": {
        "pl": "Twierdzenie.",
        "en": "Theorem.",
    },
    "ch.explore.math.proof": {
        "pl": "Dowod.",
        "en": "Proof.",
    },
    "ch.explore.math.qed": {
        "pl": "C.B.D.U.",
        "en": "Q.E.D.",
    },
    "ch.explore.math.binder.let": {
        "pl": "Niech {name} : {type}.",
        "en": "Let {name} : {type}.",
    },
    "ch.explore.math.binder.given": {
        "pl": "Dla danego {name} : {type},",
        "en": "Given {name} : {type},",
    },
    "ch.explore.math.case_analysis": {
        "pl": "Analiza przypadkow wzgledem {name}.",
        "en": "By case analysis on {name}.",
    },
    "ch.explore.math.induction.intro": {
        "pl": "Indukcja po {name}.",
        "en": "By induction on {name}.",
    },
    "ch.explore.math.induction.base": {
        "pl": "Krok bazowy:",
        "en": "Base case:",
    },
    "ch.explore.math.induction.step": {
        "pl": "Krok indukcyjny (z hipoteza ih):",
        "en": "Inductive step (with IH):",
    },
    "ch.explore.lemmas_footer.title": {
        "pl": "Uzyte lematy",
        "en": "Lemmas referenced",
    },
    "ch.explore.narrative.title": {
        "pl": "Parafraza narracyjna",
        "en": "Narrative paraphrase",
    },
    "ch.explore.narrative.auto_label": {
        "pl": "wygenerowane automatycznie",
        "en": "auto-generated",
    },

    # ---------------------------------------------------------------------
    # Track 3 (paraphrase) keys — LLM-driven plain-language explanation.
    # ---------------------------------------------------------------------
    "ch.explore.paraphrase.title": {
        "pl": "Parafraza LLM",
        "en": "LLM paraphrase",
    },
    "ch.explore.paraphrase.unavailable": {
        "pl": "Parafraza niedostepna (brak klucza API albo blad polaczenia).",
        "en": "Paraphrase unavailable (no API key or network error).",
    },
    "ch.explore.paraphrase.fetching": {
        "pl": "Pobieram parafraze z modelu LLM...",
        "en": "Fetching paraphrase from the LLM...",
    },
    "ch.explore.paraphrase.cached_label": {
        "pl": "(z cache)",
        "en": "(from cache)",
    },
    "ch.explore.paraphrase.no_key_hint": {
        "pl": "Dodaj OPENAI_API_KEY do ~/.config/openai/env aby wlaczyc.",
        "en": "Add OPENAI_API_KEY to ~/.config/openai/env to enable.",
    },
    "ch.explore.toggle_paraphrase": {
        "pl": "Parafraza LLM: {state}.",
        "en": "LLM paraphrase: {state}.",
    },
    "ch.explore.paraphrase.usage": {
        "pl": "--paraphrase: pobierz parafraze LLM od razu po pobraniu termu (potrzeba OPENAI_API_KEY).",
        "en": "--paraphrase: fetch the LLM paraphrase eagerly once the term is loaded (requires OPENAI_API_KEY).",
    },
    "ch.explore.paraphrase.panel_hint": {
        "pl": "Parafraza wygenerowana przez model LLM - traktuj jako dodatek, nie zrodlo prawdy.",
        "en": "Paraphrase generated by an LLM - treat it as an aid, not a source of truth.",
    },
    "ch.explore.paraphrase.cache_hit": {
        "pl": "Trafienie cache parafrazy.",
        "en": "Paraphrase cache hit.",
    },
    "ch.explore.paraphrase.cache_miss": {
        "pl": "Brak w cache - wykonuje zapytanie do API.",
        "en": "Cache miss - calling the API.",
    },

    # ---------------------------------------------------------------------
    # EML keys — dashboard subcommand for arXiv:2603.21852 formalization.
    # ---------------------------------------------------------------------
    "eml.help.title": {
        "pl": "EML - dashboard formalizacji (arXiv:2603.21852)",
        "en": "EML - formalization dashboard (arXiv:2603.21852)",
    },
    "eml.help.body": {
        "pl": (
            "Subkomendy:\n"
            "  eml list [--status S] [--difficulty N]   tabela kawalkow\n"
            "  eml show <id>                            pokaz tresc kawalka i Lean\n"
            "  eml tree                                 graf zaleznosci\n"
            "  eml status                               podsumowanie liczbowe\n"
            "  eml submit <id> [--all-pending] [--limit N]   wyslij do Aristotle\n"
            "  eml watch <id> [--all]                   pobierz rozwiazanie\n"
            "  eml verify [<id>]                        lake env lean\n"
            "  eml combine [--pdf] [--html]             zlozony raport\n"
            "  eml refresh-paper                        instrukcja recznej aktualizacji"
        ),
        "en": (
            "Subcommands:\n"
            "  eml list [--status S] [--difficulty N]   chunk table\n"
            "  eml show <id>                            show chunk + Lean target\n"
            "  eml tree                                 dependency graph\n"
            "  eml status                               numeric summary\n"
            "  eml submit <id> [--all-pending] [--limit N]   submit to Aristotle\n"
            "  eml watch <id> [--all]                   download solution\n"
            "  eml verify [<id>]                        lake env lean\n"
            "  eml combine [--pdf] [--html]             assembled report\n"
            "  eml refresh-paper                        manual refresh instructions"
        ),
    },
    "eml.list.col.id": {"pl": "id", "en": "id"},
    "eml.list.col.title": {"pl": "tytul", "en": "title"},
    "eml.list.col.kind": {"pl": "rodzaj", "en": "kind"},
    "eml.list.col.difficulty": {"pl": "trudnosc", "en": "difficulty"},
    "eml.list.col.status": {"pl": "status", "en": "status"},
    "eml.list.col.deps": {"pl": "zaleznosci", "en": "deps"},
    "eml.list.col.project": {"pl": "project_id", "en": "project_id"},
    "eml.list.title": {
        "pl": "EML - kawalki ({count})",
        "en": "EML - chunks ({count})",
    },
    "eml.list.no_chunks": {
        "pl": "Brak kawalkow - workspace jeszcze niezasiany.",
        "en": "No chunks yet - workspace not seeded.",
    },
    "eml.show.title": {
        "pl": "EML kawalek: {chunk_id}",
        "en": "EML chunk: {chunk_id}",
    },
    "eml.show.no_chunk": {
        "pl": "Nie znalazlem kawalka pasujacego do '{prefix}'.",
        "en": "No chunk matched '{prefix}'.",
    },
    "eml.show.section.paper": {"pl": "Cytat z artykulu", "en": "Paper quote"},
    "eml.show.section.informal": {"pl": "Tresc nieformalna", "en": "Informal text"},
    "eml.show.section.lean": {"pl": "Cel Lean", "en": "Lean target"},
    "eml.show.section.status": {"pl": "Status", "en": "Status"},
    "eml.show.no_target": {
        "pl": "(brak target.lean - jeszcze nie zasiany)",
        "en": "(no target.lean - not seeded yet)",
    },
    "eml.tree.title": {
        "pl": "EML - drzewo zaleznosci",
        "en": "EML - dependency tree",
    },
    "eml.tree.cycle": {
        "pl": "(cykl wykryty)",
        "en": "(cycle detected)",
    },
    "eml.tree.no_chunks": {
        "pl": "Drzewo puste - brak kawalkow.",
        "en": "Tree empty - no chunks.",
    },
    "eml.status.summary": {
        "pl": "EML: pending={pending} submitted={submitted} complete={complete} failed={failed} (pokrycie {coverage}%, n={total})",
        "en": "EML: pending={pending} submitted={submitted} complete={complete} failed={failed} (coverage {coverage}%, n={total})",
    },
    "eml.status.empty": {
        "pl": "EML: brak kawalkow (workspace pusty).",
        "en": "EML: no chunks (empty workspace).",
    },
    "eml.submit.usage": {
        "pl": "uzycie: eml submit <chunk-id> [--all-pending] [--limit N]",
        "en": "usage: eml submit <chunk-id> [--all-pending] [--limit N]",
    },
    "eml.submit.resolving": {
        "pl": "Rozpoznaje kawalek '{prefix}'...",
        "en": "Resolving chunk '{prefix}'...",
    },
    "eml.submit.submitting": {
        "pl": "Wysylam kawalek {chunk_id} do Aristotle...",
        "en": "Submitting chunk {chunk_id} to Aristotle...",
    },
    "eml.submit.ok": {
        "pl": "Wyslano {chunk_id}; project_id={project_id}",
        "en": "Submitted {chunk_id}; project_id={project_id}",
    },
    "eml.submit.err": {
        "pl": "Blad podczas wysylki {chunk_id}: {error}",
        "en": "Submission error for {chunk_id}: {error}",
    },
    "eml.submit.no_dependencies_met": {
        "pl": "Pomijam {chunk_id}: nie wszystkie zaleznosci ukonczone ({missing}).",
        "en": "Skipping {chunk_id}: not all dependencies complete ({missing}).",
    },
    "eml.submit.already_complete": {
        "pl": "Pomijam {chunk_id}: status={status}.",
        "en": "Skipping {chunk_id}: status={status}.",
    },
    "eml.submit.batch_summary": {
        "pl": "Wysylka wsadowa: udane={ok}, pominiete={skipped}, bledy={failed}.",
        "en": "Batch submit: ok={ok}, skipped={skipped}, failed={failed}.",
    },
    "eml.submit.no_target": {
        "pl": "Brak target.lean dla {chunk_id} - kawalek nie jest gotowy.",
        "en": "No target.lean for {chunk_id} - chunk not ready.",
    },
    "eml.watch.polling": {
        "pl": "Czekam na ukonczenie {chunk_id} (project_id={project_id})...",
        "en": "Polling for {chunk_id} (project_id={project_id})...",
    },
    "eml.watch.saved": {
        "pl": "Zapisano rozwiazanie do {path}.",
        "en": "Saved solution to {path}.",
    },
    "eml.watch.err": {
        "pl": "Blad watch dla {chunk_id}: {error}",
        "en": "Watch error for {chunk_id}: {error}",
    },
    "eml.watch.no_project": {
        "pl": "Brak project_id dla {chunk_id} - najpierw uzyj 'eml submit'.",
        "en": "No project_id for {chunk_id} - run 'eml submit' first.",
    },
    "eml.watch.no_lean_files": {
        "pl": "Aristotle nie zwrocil zadnych plikow .lean dla {chunk_id}.",
        "en": "Aristotle returned no .lean files for {chunk_id}.",
    },
    "eml.verify.ok": {
        "pl": "Weryfikacja {chunk_id} OK.",
        "en": "Verification of {chunk_id} OK.",
    },
    "eml.verify.err": {
        "pl": "Weryfikacja {chunk_id} NIEPOWODZENIE (rc={rc}).",
        "en": "Verification of {chunk_id} FAILED (rc={rc}).",
    },
    "eml.verify.no_artifact": {
        "pl": "Brak pliku do weryfikacji dla {chunk_id} ({path}).",
        "en": "No artifact to verify for {chunk_id} ({path}).",
    },
    "eml.verify.no_workspace": {
        "pl": "Brak lean_workspace - nie mozna uruchomic 'lake env lean'.",
        "en": "No lean_workspace - cannot run 'lake env lean'.",
    },
    "eml.combine.building": {
        "pl": "Buduje raport: {path}",
        "en": "Building report: {path}",
    },
    "eml.combine.pdf_done": {
        "pl": "PDF gotowy: {path}",
        "en": "PDF ready: {path}",
    },
    "eml.combine.html_done": {
        "pl": "HTML gotowy: {path}",
        "en": "HTML ready: {path}",
    },
    "eml.combine.no_chunks": {
        "pl": "Brak kawalkow do zlozenia raportu.",
        "en": "No chunks to assemble into a report.",
    },
    "eml.combine.no_pandoc": {
        "pl": "Brak pandoc/xelatex - PDF pominiety.",
        "en": "Missing pandoc/xelatex - skipping PDF.",
    },
    "eml.unknown_sub": {
        "pl": "Nieznana subkomenda 'eml': {sub}",
        "en": "Unknown 'eml' subcommand: {sub}",
    },
    "eml.unknown_sub_hint": {
        "pl": "Sprobuj 'eml' (bez argumentow) zeby zobaczyc liste.",
        "en": "Try 'eml' (no args) to see the list.",
    },
    "eml.no_paper": {
        "pl": "EML workspace nie zainicjowany - uruchom setup (proofs/eml/2603_21852).",
        "en": "EML workspace not initialized - run setup (proofs/eml/2603_21852).",
    },
    "eml.refresh.body": {
        "pl": "Aktualizacja recznie: edytuj source/paper_extracted.md i uruchom decomposition.",
        "en": "Manual fetch required, see source/paper_extracted.md.",
    },
    "eml.parse_err": {
        "pl": "Blad parsowania argumentow eml: {error}",
        "en": "Failed to parse eml arguments: {error}",
    },

    # ---- Acorn keys ----
    "ac.help.title": {
        "pl": "ac (acorn)",
        "en": "ac (acorn)",
    },
    "ac.help.body": {
        "pl": (
            "[bold]ac[/bold] (alias [bold]acorn[/bold]) — Acorn theorem prover (Rust + lokalny AI).\n\n"
            "Podkomendy:\n"
            "  [accent]key[/accent]  | keys           — sciezka binarki, wersja, biblioteka, liczba modulow\n"
            "  [accent]list[/accent]                  — lista modulow w acornlib\n"
            "  [accent]verify[/accent] <modul|plik>   — weryfikacja (modul po nazwie albo plik .ac)\n"
            "  [accent]check[/accent]  <modul>        — strict check (kazdy goal musi byc cached)\n"
            "  [accent]docs[/accent]   <modul>        — wygeneruj dokumentacje (HTML w build/docs)\n"
            "  [accent]demo[/accent]                  — twierdzenie one_plus_one z nat/basic_addition.ac\n"
            "  [accent]scratch[/accent] <snippet>     — pipe snippetu na stdin → acorn verify -\n\n"
            "[muted]Trick stdin: `ac scratch \"theorem t { 1 + 1 = 2 }\"` -> snippet\n"
            "ladowany jako pseudo-modul. Prowadzi to do `acorn verify -`.[/muted]\n\n"
            "[muted]W planach (jeszcze nie wystawione): serve (LSP), reprove, select, clean.[/muted]"
        ),
        "en": (
            "[bold]ac[/bold] (alias [bold]acorn[/bold]) — Acorn theorem prover (Rust + local AI).\n\n"
            "Subcommands:\n"
            "  [accent]key[/accent]  | keys           — binary path, version, library path, module count\n"
            "  [accent]list[/accent]                  — list modules in acornlib\n"
            "  [accent]verify[/accent] <module|file>  — run verifier (module name or .ac file)\n"
            "  [accent]check[/accent]  <module>       — strict check (every goal must be cached)\n"
            "  [accent]docs[/accent]   <module>       — generate documentation (HTML in build/docs)\n"
            "  [accent]demo[/accent]                  — one_plus_one theorem from nat/basic_addition.ac\n"
            "  [accent]scratch[/accent] <snippet>     — pipe snippet to stdin -> acorn verify -\n\n"
            "[muted]stdin trick: `ac scratch \"theorem t { 1 + 1 = 2 }\"` -> snippet\n"
            "is fed to `acorn verify -` so you can prototype without a file.[/muted]\n\n"
            "[muted]Coming later (not wired yet): serve (LSP), reprove, select, clean.[/muted]"
        ),
    },
    "ac.no_binary": {
        "pl": (
            "Nie znalazlem binarki acorn. Sprawdzilem:\n{candidates}\n\n"
            "Zainstaluj Acorn i upewnij sie, ze ktorys z tych katalogow jest na PATH."
        ),
        "en": (
            "Could not find the acorn binary. Checked:\n{candidates}\n\n"
            "Install Acorn and ensure one of these directories is on PATH."
        ),
    },
    "ac.no_lib": {
        "pl": "Brak katalogu biblioteki Acorn: {path}. Sklonuj acornlib do tej lokalizacji.",
        "en": "Acorn library directory missing: {path}. Clone acornlib into that location.",
    },
    "ac.no_output": {
        "pl": "brak wyjscia",
        "en": "no output",
    },
    "ac.spinner.interrupted": {
        "pl": "Przerwano (Ctrl-C).",
        "en": "Interrupted (Ctrl-C).",
    },
    "ac.argparse_err": {
        "pl": "Blad parsowania argumentow: {error}",
        "en": "Argument parse error: {error}",
    },
    "ac.unknown_sub": {
        "pl": "Nieznana podkomenda:",
        "en": "Unknown subcommand:",
    },
    "ac.unknown_sub_hint": {
        "pl": "Wpisz `ac`, by zobaczyc liste.",
        "en": "Type `ac` to see the list.",
    },
    "ac.key.title": {
        "pl": "Acorn — info",
        "en": "Acorn — info",
    },
    "ac.key.body": {
        "pl": (
            "[bold]Binarka:[/bold] {binary}\n"
            "[bold]Wersja:[/bold]  {version}\n"
            "[bold]Biblioteka:[/bold] {lib}\n"
            "[bold]Modulow .ac:[/bold] {modules}"
        ),
        "en": (
            "[bold]Binary:[/bold]  {binary}\n"
            "[bold]Version:[/bold] {version}\n"
            "[bold]Library:[/bold] {lib}\n"
            "[bold].ac modules:[/bold] {modules}"
        ),
    },
    "ac.list.title": {
        "pl": "Moduly acornlib ({count})",
        "en": "acornlib modules ({count})",
    },
    "ac.list.col.module": {
        "pl": "modul",
        "en": "module",
    },
    "ac.verify.usage": {
        "pl": "Uzycie: ac verify <modul-lub-plik>",
        "en": "Usage: ac verify <module-or-file>",
    },
    "ac.verify.running": {
        "pl": "acorn verify {target}",
        "en": "acorn verify {target}",
    },
    "ac.verify.ok": {
        "pl": "verify OK · {target}",
        "en": "verify OK · {target}",
    },
    "ac.verify.fail": {
        "pl": "verify FAIL · {target} (rc={rc})",
        "en": "verify FAIL · {target} (rc={rc})",
    },
    "ac.check.usage": {
        "pl": "Uzycie: ac check <modul>",
        "en": "Usage: ac check <module>",
    },
    "ac.check.running": {
        "pl": "acorn check {target}",
        "en": "acorn check {target}",
    },
    "ac.check.ok": {
        "pl": "check OK · {target}",
        "en": "check OK · {target}",
    },
    "ac.check.fail": {
        "pl": "check FAIL · {target} (rc={rc})",
        "en": "check FAIL · {target} (rc={rc})",
    },
    "ac.docs.usage": {
        "pl": "Uzycie: ac docs <modul>",
        "en": "Usage: ac docs <module>",
    },
    "ac.docs.running": {
        "pl": "acorn docs -> {out}",
        "en": "acorn docs -> {out}",
    },
    "ac.docs.ok": {
        "pl": "Dokumentacja zapisana w: {out}\n\n[dim]{tail}[/dim]",
        "en": "Docs written to: {out}\n\n[dim]{tail}[/dim]",
    },
    "ac.demo.title": {
        "pl": "ac demo — one_plus_one",
        "en": "ac demo — one_plus_one",
    },
    "ac.demo.body": {
        "pl": (
            "[bold]Demo Acorn[/bold] — najmniejsze, dydaktyczne twierdzenie z biblioteki standardowej.\n\n"
            "Twierdzenie [accent]{theorem}[/accent] zyje w module [bold]{module}[/bold]\n"
            "(plik: [muted]{file}[/muted]).\n\n"
            "Acorn weryfikuje arytmetyke Peana lokalnym solverem AI. Po wywolaniu zobaczysz\n"
            "modul w cale — `1 + 1 = 2` to pierwszy z setki faktow z dodawania jednocyfrowego."
        ),
        "en": (
            "[bold]Acorn demo[/bold] — the smallest, didactic theorem from the standard library.\n\n"
            "Theorem [accent]{theorem}[/accent] lives in module [bold]{module}[/bold]\n"
            "(file: [muted]{file}[/muted]).\n\n"
            "Acorn verifies Peano arithmetic with its built-in local AI solver. After this run\n"
            "you will see the whole module — `1 + 1 = 2` is the first of a hundred single-digit\n"
            "addition facts."
        ),
    },
    "ac.demo.running": {
        "pl": "acorn verify {module} (demo)",
        "en": "acorn verify {module} (demo)",
    },
    "ac.scratch.usage": {
        "pl": (
            "Uzycie: ac scratch \"<snippet .ac>\"\n"
            "Snippet trafia na stdin do `acorn verify -`. Przyklad:\n"
            "  ac scratch \"theorem t { 1 + 1 = 2 }\""
        ),
        "en": (
            "Usage: ac scratch \"<.ac snippet>\"\n"
            "The snippet is piped on stdin to `acorn verify -`. Example:\n"
            "  ac scratch \"theorem t { 1 + 1 = 2 }\""
        ),
    },
    "ac.scratch.running": {
        "pl": "acorn verify - (stdin)",
        "en": "acorn verify - (stdin)",
    },
}


def t(key: str, **kwargs: Any) -> str:
    """Translate ``key`` to current language; format with ``kwargs`` if given.

    Fallback chain: current → PL → klucz dosłownie.
    """
    bundle = STRINGS.get(key)
    if bundle is None:
        return key
    text = bundle.get(_LANG) or bundle.get("pl") or key
    if kwargs:
        try:
            return text.format(**kwargs)
        except (KeyError, IndexError):
            return text
    return text
