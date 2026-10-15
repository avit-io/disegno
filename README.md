# Disegno

Un linguaggio totale, con tipi dipendenti, per CI/CD e infrastruttura. Progetta, non esegue: un programma Disegno dichiara un piano, il type checker ne prova le proprietà, [Dagger](https://dagger.io) lo realizza.

```
(def go-build : (→ Dir Dir)
  [src] (let [root /src, out /out, bin (/ out "hello")]
          (pipe (container)
                (from "golang:1.25-alpine")                       ; un Image, verificato
                (with-mounted-cache /go/pkg/mod (cache-volume "go-mod"))
                (with-dir root src)
                (with-workdir root)
                (with-exec ["go" "build" "-o" bin "."])
                (dir-of out))))

(def main : (→ [src (Host "hello")] (Export Dir))
  [src] (overlay "bin" (go-build src)))

; teoremi, non linter: valgono per ogni sorgente
(def montaggi-disgiunti : (→ [src Dir] (Disjoint-mounts (go-build src)))
  [src] auto)
```

- **Totale**: niente ricorsione generale, copertura dei casi, universi stratificati, positività; un kernel ricontrolla ogni termine.
- **Il piano è un dato**: le operazioni del motore sono costruttori di un tipo induttivo, generati dallo schema di Dagger. Le regole che oggi stanno in linter e policy (immagini pinnate, test prima di publish, montaggi disgiunti) sono teoremi, provati per calcolo con `auto`.
- **I punti non si sommano**: i letterali si leggono secondo il tipo atteso (`"golang:1.25-alpine"` è un `Image`, `/out` è un punto); punto più punto è un errore di tipo.
- **Due tempi**: `if` decide mentre si costruisce il piano, `branch` durante l'esecuzione, su osservazioni del motore.

## Uso

Serve [Nix](https://nixos.org) con i flake e Docker. La shell avvia un motore Dagger dedicato.

```
nix develop
scheme --script disegno.ss checks.disegno              # disegno interno: tipi e teoremi
scheme --script disegno.ss go.disegno                  # disegno esterno: il piano, in GraphQL
dagger run scheme --script disegno.ss go.disegno       # opera: l'esecuzione su Dagger
scheme --script test.ss                                # i test (sotto dagger run anche dal vivo)
```

Il progetto, le scelte e le questioni aperte sono in [DESIGN.md](DESIGN.md). È un esperimento: l'ospite è Chez Scheme, il motore Dagger 0.21.
