# Wtyczki, kable i krokodyle — rzecz o rachunku lambda

Materiały do 90-minutowego wykładu popularnonaukowego dla ambitnych licealistów z klas matematycznych.

**Autor:** dr Bartosz Naskręcki
**Afiliacja:** Wydział Matematyki i Informatyki UAM w Poznaniu / Centrum Wiarygodnej Sztucznej Inteligencji, Politechnika Warszawska
**Sala:** Powietrze
**Data:** Falenty 2026

## Co znajdziesz w tym repo

| Katalog | Zawartość |
| --- | --- |
| `book/` | **JupyterBook v2** — przystępny wykład krok po kroku, od „krokodyli” Brecta Victora do rachunku Peano, Leana i AlphaGeometry. |
| `slides/` | **Prezentacja 90 min** (reveal.js + Markdown) z motywem matematyczno-graficznym, dobrze dobranymi przykładami i kolejnymi slajdami do dyskusji. |
| `lambda_lab/` | **Aplikacja terminalowa** (Python, `rich` + `textual`) — startpage, animacje, kolorowe komentarze, tryb krok po kroku dla dowodów w Pythonie, Lean 4 i AlphaGeometry. |
| `docs/` | Dokumentacja dla wykładowcy: sekwencja lekcji, karty komend `lambda_lab`, notatki wykonawcze, literatura. |
| `PLAN/` | Wielopoziomowe plany: L0 cele, L1 moduły, L2 rozdziały, L3 zadania. Każdy pas pracy ma własny plik. |
| `PLAN.md` | Widok indeksu planów. |
| `JOURNAL.md` | Dziennik prac projektowych. |

## Szybki start

```bash
# 1. Środowisko Pythona (JupyterBook + Lambda Lab)
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt

# 2. Zbuduj książkę (JupyterBook v2)
make book

# 3. Uruchom aplikację terminalową
make lab
# lub:
python -m lambda_lab
```

## Filozofia projektu

1. **Od krokodyla do Leana** — zaczynamy od zabawnej gry „Alligator Eggs”
   (Bret Victor), pokazujemy, że to rachunek λ, i kończymy w narzędziach
   weryfikacji formalnej używanych przez Amazon i DeepMind.
2. **Eksperyment zamiast definicji** — każde pojęcie wprowadzamy
   **najpierw** jako coś, co można wykonać w Pythonie lub narysować
   na kartce, a **potem** ujmujemy matematycznie.
3. **Terminal jako narzędzie magii** — `lambda_lab` wizualizuje krok po kroku
   β-redukcję, dowody Leana i proofy AlphaGeometry, aby uczniowie zobaczyli,
   że „dowody formalne” to w istocie rachunek, który można oglądać.

## Licencja

Materiały dydaktyczne — CC BY 4.0.
Kod — MIT.
