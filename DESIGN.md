# Disegno — un linguaggio totale su Dagger

Oct 15, 2026 · @Alvise Vitturi — rivisto alla fine della prima giornata di implementazione.

## Il nome

Il linguaggio si chiama Disegno, perché il nome dice quello che fa: progetta, non esegue.

Nella teoria dell'arte del Rinascimento, a partire da Vasari, il disegno è l'idea intellettuale dell'opera. Precede e governa la sua realizzazione nella materia: il colore, il marmo, la costruzione. Allo stesso modo un programma Disegno dichiara il progetto completo, tipato e totale, e lascia al motore la realizzazione.

In italiano la parola ha anche un secondo senso, quello di proposito o intento, come in "avere un disegno" o "disegno di legge". È il principio del linguaggio: l'IO esiste solo come dichiarazione di intenti.

- Il disegno è il piano puro: ciò che scrive l'utente e che il type checker verifica.
- L'esecuzione è di Dagger, governata dal nucleo fidato.

## Idea e principio

Un linguaggio alla Martin-Löf, totale, che non esegue niente: dichiara. L'IO esiste solo come dato, e l'unico interprete di quei dati è Dagger.

- **Scopo**: un linguaggio formale ed estetico per CI/CD e infrastruttura, non per algoritmi. I dati sono di dimensione ragionevole, quindi le prestazioni non contano.
- **Totalità**: niente ricorsione generale. Ogni programma termina per costruzione, e questo è una garanzia, non un limite.
- **Il piano è un dato**: le operazioni del motore sono costruttori di un tipo induttivo. Il programma costruisce un termine; il runner lo interpreta. Proprietà del piano che oggi stanno in linter e policy diventano teoremi.
- **Scelte forti**: si accettano limitazioni in cambio della purezza dell'idea e della semplicità. La parte ingegneristica entra nella semplicità: assioma K, un solo universo di default, un solo argomento decrescente. Non è HoTT. La consistenza logica invece non si negozia.

Antenati dell'idea: l'IO a richieste e risposte di Haskell 1.0, le derivazioni di Nix, i Cmd di Elm, la totalità di Dhall, i funtori applicativi selettivi.

## Stato

Funziona, dal vivo su Dagger, l'intera catena: sorgente `.disegno` → type checker → valutazione di `main` a un piano → GraphQL → sessione Dagger → export sull'host. In particolare:

- type checker con tipi dipendenti, famiglie induttive, pattern matching dipendente, controllo di copertura, terminazione strutturale, positività stretta e universi stratificati, ricontrollato da un kernel;
- piano come dato induttivo generato dallo schema di Dagger (93 costruttori);
- `branch` su osservazioni del motore, con un piano a secco per ogni esito;
- `record` con invarianti nel tipo e `auto` per le prove calcolate;
- i teoremi `prod-pinnate` e `test-prima-di-publish` del documento originale, provati con `auto`; il secondo per ogni sorgente.

## Superficie del linguaggio

Il linguaggio appare come un linguaggio a sé: dal codice non si vede l'ospite né il meccanismo di valutazione.

- Una sola forma di definizione: `def nome : tipo`, poi clausole `[pattern] corpo`, oppure un corpo solo.
- `data` per i tipi induttivi, `record` per un solo costruttore con campi nominati.
- `extern` e `include` sono riservati alla libreria standard.
- Le variabili libere nelle firme sono quantificate implicitamente. Se il tipo di una di esse non si può ricavare, lo si generalizza: `refl : (≡ x x)` diventa `{A : Type}{x : A} → x ≡ x`.
- I letterali `0, 1, 2…` sono zucchero per `zero`, `add1`; le stringhe `"…"` sono letterali di tipo `String`.
- **Le quadre sono sintassi**: in una firma `[x T]` è un binder, `(x T)` un'applicazione; in un termine `["a" "b"]` è una lista; nelle definizioni `[…]` raccoglie i pattern di una clausola o i campi di un costruttore.
- **`pipe`**: `(pipe x (f a) g)` è `(g (f x a))`. Il valore passa come primo argomento esplicito, come l'oggetto di un metodo GraphQL.
- **`auto`**: prova per calcolo (vedi Curry-Howard).
- Parole riservate: `→ Type _ pipe auto`.
- Programmi e prove si scrivono nello stesso modo: cambia solo il tipo.

```
(def +-zero : (→ [n Nat] (≡ (+ n 0) n))
  [zero]     refl
  [(add1 k)] (cong add1 (+-zero k)))

(data Vec : (→ Type Nat Type)
  [nil  : (Vec A 0)]
  [cons : (→ A (Vec A n) (Vec A (add1 n)))])

(def head : (→ (Vec A (add1 n)) A)      ; il caso nil è riconosciuto impossibile
  [(cons x _)] x)
```

Invarianti di dominio nel tipo, verificati calcolando al momento del check. `record` genera il costruttore `service` e le proiezioni `Service.name`, `Service.env`, …; i campi successivi possono dipendere dai precedenti.

```
(record Service
  [name     : String]
  [env      : Env]
  [replicas : Nat]
  [ok       : (≥ replicas (min-replicas env))])

(def api : Service
  (service "api" prod 3 auto))           ; con 2 repliche: «auto: la proposizione si riduce a ⊥»
```

## Il piano è un dato

Il linguaggio non ha primitive di IO. Le operazioni del motore sono **costruttori** di una famiglia induttiva generata dallo schema di Dagger:

```
(data Kind [Kind.container] [Kind.directory] [Kind.file] … [Kind.bool] [Kind.export])

(data Obj : (→ Kind Type)
  [Container.from      : (→ [self (Obj Kind.container)] [address String] (Obj Kind.container))]
  [Container.with-exec : (→ [self (Obj Kind.container)] [args (List String)] (Obj Kind.container))]
  [Directory.exists    : (→ [self (Obj Kind.directory)] [path String] (Obj Kind.bool))]
  …)

(def Container : Type (Obj Kind.container))
```

- **Una famiglia sola, indicizzata dal tipo GraphQL**: `Container`, `Directory`, `File` si richiamano a vicenda; con un indice non servono data mutuamente ricorsivi, e positività, copertura e universi funzionano senza casi speciali.
- **Il nome del costruttore è il campo**: `Container.with-exec` è `withExec` su `Container`; `Query.git` è un campo radice. I nomi dei binder espliciti sono gli argomenti GraphQL; `self` è l'oggetto su cui si chiama il metodo.
- **Generazione** (`gen.ss`): introspezione sulla sessione; solo i tipi in un elenco consentito (per non invadere lo spazio dei nomi dell'utente), solo gli argomenti obbligatori. Gli argomenti oggetto sono `ID` generici nello schema: il tipo vero si legge dalla direttiva `@expectedType`. `Int` diventa `Nat`, `Boolean` diventa `Bool` negli argomenti e un'osservazione `(Obj Kind.bool)` nei risultati. Il file generato, `engine.disegno`, si committa: il type checking non richiede una sessione.
- **Nomi corti**: `std.disegno` definisce `with-file`, `from`, `with-exec`, `put`, … come semplici `def` sopra i costruttori.
- **Attraversamento generato**: `nodes : (→ (Obj k) (List Any))` elenca tutti i sotto-piani per ricorsione strutturale, un caso per costruttore. Sopra di esso le proprietà si scrivono in poche righe, senza ricorsione annidata:

```
(def image-of : (→ Any (List String))
  [(any (Container.from _ address))] [address]
  [_]                                [])

(def images : (→ (Obj k) (List String))
  [p] (concat-map image-of (nodes p)))
```

Confine con l'host. Il programma dichiara cosa riceve, `(Host "percorso")` nella firma di `main`, e cosa restituisce, un `Export` (`overlay` o `replace`, cioè export con `wipe`). Il runner legge la firma prima che si riduca; il costruttore che legge l'host, `%host-dir`, è inaccessibile all'utente. Scrivere sull'host è descrivere lo stato finale.

```
(def gen-config : (→ Dir Dir)
  [src] (with-file src "config/app.toml" "porta = 8080\n"))

(def main : (→ [src (Host ".")] (Export Dir))
  [src] (overlay "." (gen-config src)))
```

## Due tempi, due condizionali

Il programma produce un piano statico, noto per intero prima dell'esecuzione. Nessun dato del mondo torna al linguaggio (niente import from derivation).

- **`if`** decide su valori noti quando si costruisce il piano. Non è una primitiva: è una `def` per casi su `Bool`.
- **`branch`** decide su osservazioni, che esistono solo durante l'esecuzione. È un **costruttore** del piano che contiene entrambi i rami; a runtime se ne sceglie solo uno.

```
(def release : (→ [src (Host ".")] (Export Dir))
  [src] (branch (passes? (test src))
          (overlay "dist" (build src))
          (overlay "reports" (report src))))
```

La distinzione di fase viene gratis dai tipi: `(Remote Bool)` non è `Bool`, quindi un'osservazione dentro un `if` è un errore di tipo, e `branch` su un `Bool` pure. Le osservazioni sono un elenco chiuso: `passes?` (exit code 0, dopo `try-exec`, che è `withExec` con `expect: ANY`) e i campi `Boolean` dello schema, come `Directory.exists`.

Il runner realizza `branch` chiedendo la condizione e sottomettendo il ramo scelto, nella stessa sessione. A secco stampa un piano per ogni combinazione di esiti, con la condizione che lo sceglie. Poiché entrambi i rami stanno nel piano, una proprietà del piano va provata su tutti e due: è l'analisi statica dei funtori applicativi selettivi (Mokhov e altri, 2019).

## Nucleo fidato

La parte sporca è piccola, chiusa e scritta da chi progetta il linguaggio.

- **Kernel** (fidato): ricontrolla ogni termine prodotto dall'elaboratore, con `Type n : Type n+1`, mai `Type : Type`. L'elaboratore (nomi, impliciti, metavariabili, pattern) può sbagliare; il kernel no.
- **Snodi**: elenco chiuso di costruttori del nucleo che il runner realizza in modo speciale: `%host-dir`, `try-exec`, `passes?`, `branch`, `overlay`, `replace`, `publish`.
- **`extern`** è rimasto solo per i tipi opachi e le primitive pure: `String` e `contains?`, che calcola sui letterali. Un extern non mente: restituisce un tipo opaco o calcola; mai una proposizione, mai un dato del mondo.
- **Runner**: l'unico posto dove si ammette il non determinismo. Realizza `branch`, `Host` ed `Export`.
- **Base fidata** complessiva: kernel, unificazione dei pattern (il kernel non ricontrolla come sono tipati), runner, generatore. Si verifica con i test; tutto il resto lo verifica il type checker.

Precedente e costo noto: Elm 0.19 ha riservato il codice nativo ai pacchetti ufficiali, garantendo la purezza dell'ecosistema a prezzo dell'estensibilità.

## Curry-Howard: si prova il disegno

I test di Disegno non sono unit test ma proposizioni, e le loro prove sono teoremi. Si prova che il disegno è pulcro, non che lo scultore lo esegua esatto.

Condizioni di consistenza, tutte implementate e coperte da un test di rifiuto:

| Condizione | Come | Rifiutato, per esempio |
|---|---|---|
| Totalità | ricorsione strutturale su un argomento fisso | `(def assurdo : ⊥ assurdo)` |
| Copertura | divisione dei casi tipata; i casi con indici inconciliabili sono impossibili | `pred` senza `zero` |
| Universi | stratificati, verificati dal kernel; un campo di livello maggiore non sta nel data | `(def t : Type Type)`, `(data U : Type [u : (→ Type U)])` |
| Positività | stretta, sul dominio normalizzato | `(data Cattivo [mk (→ Cattivo ⊥)])` |
| Niente scappatoie | niente postulati: una `def` deve avere un corpo; `extern` solo nella libreria standard | `(def postulato : ⊥)` |
| Snodi che non mentono | i costruttori non possono mentire per costruzione; gli extern restituiscono solo tipi opachi | `(extern mente : (→ Dir ⊥) …)` |

**`auto`**: le proposizioni decidibili si scrivono `(So (test? …))`, che calcolando diventa `⊤` o `⊥`. `auto` è `tt` quando il tipo atteso si riduce a `⊤`, `refl` quando è un'uguaglianza; il kernel ricontrolla. Con dati concreti la prova si calcola:

```
(def prod-plan : Container
  (pipe (container)
        (from "alpine@sha256:4bcff639…")
        (with-exec ["echo" "ciao"])))

(def prod-pinnate : (All pinned? (images prod-plan))
  auto)
```

**Proprietà d'ordine.** Le uscite del piano sono `overlay`, `replace` e `publish`, scelte dai `branch`. `effects` elenca ogni uscita con le osservazioni che devono essere vere perché avvenga; `(Before test? publish? p)` dice che ogni pubblicazione è protetta da un test. `effects` non scende nelle directory, quindi la prova per calcolo vale anche con un input astratto, cioè per ogni sorgente:

```
(def release : (→ Dir (Export Dir))
  [src] (branch (passes? (test src))
          (publish (image src) "registry.example.com/app:1")
          (overlay "reports" (report src))))

(def test-prima-di-publish : (→ [src Dir] (Before test? publish? (release src)))
  [src] auto)
```

Una pubblicazione scoperta, protetta da un'osservazione che non è un test (`exists?`) o messa nel ramo "falso" viene rifiutata.

**Cosa resta empirico**: che i test passino o che il binario funzioni sono osservazioni, non proposizioni. Gli unit test del codice dentro i container restano e li esegue Dagger.

## Runtime e ospite

Dagger è la piattaforma, come la BEAM per Gleam. L'ospite è Chez Scheme 10. Il linguaggio non è un SDK Dagger: il runner è un client di una sessione.

- **Sessione**: con Dagger 0.21 si usa `dagger run`, che mette `DAGGER_SESSION_PORT` e `DAGGER_SESSION_TOKEN` nell'ambiente (il documento originale citava `dagger api with-session`, che è della 1.0).
- **Trasporto**: POST su `http://127.0.0.1:$DAGGER_SESSION_PORT/query`, token come utente basic auth. Il client HTTP è scritto a mano (FFI su `socket`/`connect` di libc, HTTP/1.0 senza TLS su localhost), con un parser JSON minimo: poco codice, nel nucleo.
- **Richieste**: una catena è un documento GraphQL e parte in una richiesta. **Correzione al documento originale**: quando un oggetto è argomento di un altro (una Dir passata a `withDirectory`), non può stare nella stessa query, perché GraphQL non accetta una selezione come argomento. Il runner chiede prima il suo `id` e poi lo passa. Il piano resta statico; le richieste non sono sempre una sola.
- **Ordine**: le richieste partono in ordine deterministico, da sinistra a destra.

Perché Chez: nella tesi "tutto su Dagger" l'ecosistema dell'ospite non conta; serve un substrato minimale per un evaluator nostro (NbE, elaborazione, piano). Racket gira su Chez, quindi Chez toglie uno strato; Idris 2 compila verso Chez.

Precedente sul lato Dagger: Dang, il linguaggio nativo di Dagger 1.0, conferma che un linguaggio il cui runtime è Dagger è percorribile. Disegno si colloca come un Dang con Martin-Löf, totalità e piano ispezionabile.

## Architettura

| File | Ruolo |
|---|---|
| `core.ss` | nucleo: stampa GraphQL, HTTP su socket, JSON, sessione |
| `types.ss` | elaboratore e kernel: NbE, unificazione, pattern, copertura, terminazione, positività, `record`, `auto` |
| `plan.ss` | runner: dal piano (dato) al GraphQL, `branch`, esecuzione e piani a secco |
| `gen.ss` | generatore di `engine.disegno` dallo schema |
| `std.disegno` | libreria standard: uguaglianza, `Bool`, `Nat`, liste, nomi corti, `Host`, `Export`, proprietà del piano |
| `engine.disegno` | generato: `Kind`, `Obj`, alias, `nodes` |
| `examples.disegno`, `io.disegno`, `release.disegno` | gli esempi del documento |
| `disegno.ss` | driver: `scheme --script disegno.ss prog.disegno` stampa i piani; sotto `dagger run` li esegue |
| `test.ss` | test: nucleo, tipi, rifiuti, piani a secco e, sotto `dagger run`, dal vivo |
| `flake.nix` | ambiente: Chez, Dagger, motore dedicato con le CA dell'host |

Ambiente: `env -u LD_LIBRARY_PATH nix develop -c …`. Il motore Dagger gira in un container dedicato (`disegno-engine`) che monta il bundle CA dell'host, per attraversare il proxy TLS aziendale; il motore passa le CA anche ai container che esegue.

## Limitazioni accettate

In cambio della purezza e della semplicità:

- niente ricorsione generale e niente IO diretto;
- niente piano dinamico: i dati del mondo non tornano mai al linguaggio;
- snodi chiusi: l'utente non estende né gli extern né i costruttori del nucleo;
- la totalità vale per la descrizione, non per l'esecuzione: un comando in container può restare non deterministico;
- ciò che non passa da Dagger è di seconda classe, raggiungibile solo tramite comandi in container;
- assioma K: il pattern matching unifica `x = x`;
- un tipo che non si ricava è `Type₀`; niente polimorfismo di universo;
- terminazione con un solo argomento decrescente fisso (Ackermann è rifiutato);
- solo gli argomenti obbligatori dei campi del motore; i tipi del motore sono un elenco consentito;
- l'argomento di `Remote` ed `Export` è per ora documentazione: esistono solo osservazioni booleane ed export di directory;
- `auto` prova solo su dati concreti; un exit code vale vero se è 0 (convenzione nel runner).

## Questioni aperte

- [x] Quale primitiva usa un client per leggere l'host: `host.directory` in Dagger 0.21. Da riverificare con Workspace in Dagger 1.0.
- [ ] Export o Changeset per scrivere. Oggi export classico (`overlay`, `replace` con `wipe`).
- [ ] Il Changeset rappresenta anche le cancellazioni? Deciderebbe se servono ancora due costruttori di export.
- [x] Quali osservazioni ammettere e come tiparle: elenco chiuso, `(Obj Kind.bool)`. Resta da tipare osservazioni non booleane, con un `Kind` indicizzato.
- [ ] Tipi raffinati per CIDR, porte, tag e digest delle immagini.
- [ ] IaC: come recuperare tipi utili quando l'infrastruttura passa da comandi in container.
- [x] Proprietà d'ordine, come `test-prima-di-publish`: `publish` è un'uscita del piano, `Before` si prova per ogni input.
- [ ] Teoremi generali sui piani (`pin-corretto`): principio d'induzione generato per `Obj`, o lemmi sopra `nodes`.
- [ ] Messaggi di `auto` che mostrino la proposizione originale, non solo la sua riduzione.
- [ ] Passaggio a Dagger 1.0 quando il flake lo rende disponibile.

## Fonti

- Client libraries e GraphQL diretto, Dagger
- Endpoint HTTP della sessione
- Dang SDK, Dagger 1.0-beta
- Tipi dell'API Dagger: accesso all'host
- Export di artefatti verso l'host
- A. Kovács, elaboration-zoo (elaborazione con NbE e metavariabili)
- A. Mokhov, G. Lukyanov, S. Marlow, J. Dimino, *Selective Applicative Functors*, 2019
