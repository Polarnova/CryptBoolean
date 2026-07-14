# CryptBoolean agent guide

CryptBoolean follows the same proof-first workflow as FABL, with Carlet as the primary statement spine and FABL as a pinned upstream dependency.

## Boundaries

- Production Lean lives under `CryptBoolean/` and is pure mathematics only.
- PDF extraction, inventory editing, Blueprint rendering, CI, and audits live at the perimeter.
- The root module `CryptBoolean.lean` is the verified production surface; files unreachable from it are not complete library artifacts.
- The local Carlet and Cusick--Stănică PDFs are source references only. Do not commit them or generated extraction/render artifacts.

## Dependency policy

- FABL is imported from Git at revision `34334a1b0c8dd806c076444a0875caf29ba5e248`.
- Before adding a local declaration, search pinned FABL and Mathlib for an existing type, definition, or theorem.
- Local declarations must be cryptographic concepts, representation bridges, or proof lemmas used by a production theorem.
- Do not identify Carlet's unnormalized Walsh transform with FABL's normalized Fourier coefficient without the explicit scaling theorem.

## Formalization loop

1. Add or refine source-facing inventory in `inventory/`.
2. Add the minimal Lean signature under the relevant chapter module.
3. Record the reviewed statement dependency in the Blueprint source.
4. Close dependency-ready leaves before opening broader theorem nodes.
5. Use isolated temporary WIP files for exploratory `sorry`; do not commit or root-import them.
6. Run the narrowest module build, then the root build.
7. Run the forbidden-token, axiom, Blueprint, and fidelity audits before claiming closure.

## Verification commands

```bash
lake build CryptBoolean
./scripts/forbidden_tokens.sh
./scripts/audit_axioms.sh
./blueprint-verso/scripts/site.sh
```
