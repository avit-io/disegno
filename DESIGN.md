# Disegno — un linguaggio totale su Dagger

Oct 15, 2026 · @Alvise Vitturi — rivisto alla fine della prima giornata di implementazione. Le scelte del linguaggio, con le ragioni e i costi, sono in [ARCHITECTURE.md](ARCHITECTURE.md).

## Il nome

Il linguaggio si chiama Disegno, perché il nome dice quello che fa: progetta, non esegue.

Nella teoria dell'arte del Rinascimento, a partire da Vasari, il disegno è l'idea intellettuale dell'opera. Precede e governa la sua realizzazione nella materia: il colore, il marmo, la costruzione. Allo stesso modo un programma Disegno dichiara il progetto completo, tipato e totale, e lascia al motore la realizzazione.

Vasari lo definisce così, nel capitolo "Che cosa sia disegno" dell'introduzione alle *Vite* (1568): il disegno, "padre delle tre arti nostre, architettura, scultura e pittura, procedendo dall'intelletto, cava di molte cose un giudizio universale", e "altro non sia che una apparente espressione e dichiarazione del concetto che si ha nell'animo". *Dichiarazione* è la parola giusta: è il principio del linguaggio.

In italiano la parola ha anche un secondo senso, quello di proposito o intento, come in "avere un disegno" o "disegno di legge". L'IO esiste solo come dichiarazione di intenti.

### Disegno interno, disegno esterno, opera

Federico Zuccari, nell'*Idea de' pittori, scultori et architetti* (1607), sviluppa Vasari distinguendo due disegni: il **disegno interno**, l'idea formata nell'intelletto prima di ogni realizzazione, e il **disegno esterno**, la sua espressione sensibile, la forma tracciata sul foglio. Poi viene l'opera, nella materia. Disegno ha esattamente questi tre momenti, e sono tre usi dello stesso programma:

| Momento | In Zuccari | In Disegno | Comando |
|---|---|---|---|
| Disegno interno | l'idea nell'intelletto | il programma tipato, con i suoi teoremi: ciò che il type checker verifica | `disegno check tests/checks.disegno` |
| Disegno esterno | la forma visibile sul foglio | il piano stampato, un GraphQL per ogni esito dei `branch`, ispezionabile prima di eseguire | `disegno plan prog.disegno` |
| Opera | la realizzazione nella materia | l'esecuzione su Dagger, governata dal nucleo fidato | `disegno run prog.disegno` |

La distinzione non è decorativa. Tutto ciò che si prova sta nel disegno interno: i teoremi parlano del piano come dato, non della sua esecuzione. Il disegno esterno è ciò che si rivede, come un diff o una pull request: è determinato per intero dal disegno interno, e a secco non tocca il motore. L'opera è l'unico momento in cui entra il mondo, con le osservazioni di `branch`, e l'unico in cui il non determinismo è ammesso. Si prova che il disegno è pulcro, non che lo scultore lo esegua esatto.

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
- i teoremi `prod-pinnate` e `test-prima-di-publish` del documento originale, provati con `auto`; il secondo per ogni sorgente;
- letterali raffinati (`Image`, percorsi) e lo spazio affine dei percorsi, con la legge `q ⊕ (p ⊖ q) = p` dimostrata per induzione.

## Superficie del linguaggio

Il linguaggio appare come un linguaggio a sé: dal codice non si vede l'ospite né il meccanismo di valutazione.

- Una sola forma di definizione: `def nome : tipo`, poi clausole `[pattern] corpo`, oppure un corpo solo.
- `data` per i tipi induttivi, `record` per un solo costruttore con campi nominati, anche con parametri: `(record (Affine P V [≤ (→ P P Type)]) …)`.
- `extern` e `builtin` sono riservati alla libreria standard. Un programma vede il prelude (la logica) e importa il resto per nome: `(import dagger time)` carica `lib/dagger.disegno` e `lib/time.disegno`, una volta sola, in un unico spazio di nomi. Il nome è una parola, non un percorso: un programma non fa caricare con i privilegi della libreria un file suo.
- Le variabili libere nelle firme sono quantificate implicitamente, se hanno la forma di una variabile: una lettera, poi eventualmente cifre (`A`, `x`, `n2`). Ogni altro nome libero è un nome sconosciuto, così un `Port` senza `(import net)` è un errore e non un tipo qualsiasi. Se il tipo di una variabile non si può ricavare, lo si generalizza: `refl : (≡ x x)` diventa `{A : Type}{x : A} → x ≡ x`.
- I letterali `0, 1, 2…` sono zucchero per `zero`, `add1`; le stringhe `"…"` sono letterali di tipo `String`.
- **Le quadre sono sintassi**: in una firma `[x T]` è un binder, `(x T)` un'applicazione; in un termine `["a" "b"]` è una lista; nelle definizioni `[…]` raccoglie i pattern di una clausola o i campi di un costruttore.
- **`pipe`**: `(pipe x (f a) g)` è `(g (f x a))`. Il valore passa come primo argomento esplicito, come l'oggetto di un metodo GraphQL.
- **Letterali secondo il tipo**: `"golang:1.25-alpine"` è un `Image`, `/out` è un punto (vedi I punti non si sommano).
- **Nomi dello schema senza prefisso**: lo schema non affiora nel programma. `(with-mounted-cache c …)` si risolve in `Container.with-mounted-cache` perché `c` è un `Container`: le collisioni tra tipi le risolve il checker, non il programmatore. Un nome senza metodo adatto è un campo radice, cioè una funzione di primo livello: `(container)`, `(cache-volume "go-mod")`. Il primo argomento si elabora una volta sola, quindi dentro `pipe` la risoluzione resta lineare.
- **`auto`**: prova per calcolo (vedi Curry-Howard).
- Parole riservate: `→ Type _ pipe auto let`.
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
- **Generazione** (`tools/gen.ss`): introspezione sulla sessione; solo i tipi in un elenco consentito (per non invadere lo spazio dei nomi dell'utente), solo gli argomenti obbligatori. Gli argomenti oggetto sono `ID` generici nello schema: il tipo vero si legge dalla direttiva `@expectedType`. `Int` diventa `Nat`, `Boolean` diventa `Bool` negli argomenti e un'osservazione `(Obj Kind.bool)` nei risultati. Il file generato, `lib/engine.disegno`, si committa: il type checking non richiede una sessione.
- **Nomi curati**: i campi si scrivono senza prefisso (vedi Superficie); `dagger.disegno` aggiunge solo i nomi che rinominano davvero, come `with-file` (`withNewFile`), `with-dir`, `dir-of`, `put`, `exists?`.
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

## I punti non si sommano

È il motto di Disegno: un'operazione senza senso geometrico non si può nemmeno scrivere.

**Il problema.** Nel codice di CI e infrastruttura quasi tutto è una stringa: percorsi, immagini, indirizzi, durate. Le stringhe nascondono una distinzione che causa molti errori, quella tra posizioni e spostamenti. Un percorso assoluto scambiato per uno relativo, un istante per una durata, un indirizzo per un offset: per una stringa sono tutti uguali.

**Tre strati.** L'idea generale sono i letterali raffinati; lo spazio affine è la forma che prendono quelli con posizioni e spostamenti; le regioni sono uno strato a parte.

1. **Letterali raffinati.** I letterali restano familiari, ma è il tipo atteso a decidere come leggerli. Si scrive ancora `"golang:1.25-alpine"` o `/out`, ma dove serve un'immagine il letterale diventa un `Image`, e dove serve un percorso diventa un punto. Un letterale malformato è un errore di tipo (`«Golang:1.25» non è un Image valido`), non un fallimento dentro un container. Sotto, un tipo raffinato è una coppia Σ, il valore più la prova che è valido: `(record Image [raw : String] [ok : (So (image-ref? raw))])`. Nell'elaboratore c'è una regola sola: un costruttore il cui primo campo accoglie il valore e i cui campi restanti sono proposizioni fa da coercizione, e le prove le calcola `auto`.
2. **Spazio affine** per i valori con posizioni e spostamenti. Uno spazio affine distingue i punti dagli spostamenti, con tre regole: punto + spostamento = punto; punto − punto = spostamento; punto + punto non esiste.
3. **Regioni**: sottoalberi, blocchi CIDR, intervalli di porte. Le loro proposizioni naturali sono il contenimento e la disgiunzione: subnet disgiunte, montaggi che non si sovrappongono, porte non allocate due volte. Sono teoremi sul disegno, nel senso della sezione su Curry-Howard.

**La struttura nel linguaggio.** La differenza tra punti richiede una prova di relazione come argomento, quindi esiste solo dove ha senso. La relazione è un parametro: per i percorsi è il contenimento, per i gruppi veri (tempo, indirizzi) è sempre vera.

```
(record (Affine P V [≤ (→ P P Type)])
  [+   : (→ P V P)]
  [-   : (→ [p P] [q P] (≤ p q) V)]
  [law : (→ [p P] [q P] [h (≤ p q)] (≡ (+ q (- p q h)) p))])
```

Le leggi, come `law`, sono teoremi dimostrati una volta nella libreria standard: chi scrive un disegno le eredita. Gli operatori si chiamano `Abs.⊕`, `Instant.⊕`, `Ip.⊕`…, e la risoluzione guidata dal tipo sceglie quello giusto dal primo argomento: `(⊕ /out "bin")` è un percorso, `(⊕ inizio "1h")` un istante. `Affine` serve a enunciare e dimostrare che un dominio è un'istanza, senza bisogno di type class nel linguaggio.

**I percorsi, implementati.**

```
(data Abs [root] [/ Abs Segment])           ; punti: /out è (/ root "out")
(data Rel [here] [step Rel Segment])        ; vettori: "bin/hello"

(data ⊑ : (→ Abs Abs Type)                  ; (⊑ p q): p sta dentro q
  [⊑-refl : (⊑ p p)]
  [⊑-step : (→ (⊑ p q) (⊑ (/ p s) q))])

(def ⊖ : (→ [p Abs] [q Abs] (⊑ p q) Rel)    ; la differenza si calcola sulla prova
  [p       q ⊑-refl]     here
  [(/ p s) q (⊑-step h)] (step (⊖ p q h) s))

(def ⊕-⊖ : (→ [p Abs] [q Abs] [h (⊑ p q)] (≡ (⊕ q (⊖ p q h)) p))
  [p       q ⊑-refl]     refl
  [(/ p s) q (⊑-step h)] (cong (/s s) (⊕-⊖ p q h)))

(def percorsi : (Affine Abs Rel ⊑)
  (affine ⊕ ⊖ ⊕-⊖))
```

Il contenimento è una relazione **induttiva**, non un test booleano. Così la differenza si calcola per ricorsione sulla prova, e la legge si dimostra per induzione senza mai confrontare due stringhe: il nucleo non guadagna postulati. Sui punti concreti la prova di contenimento la trova `auto`, componendo costruttori: `(⊖ /out/bin/hello /out auto)` è il vettore `"bin/hello"`, mentre `(⊖ /out /src auto)` è un errore (`nessuna prova di (⊑ /out /src)`), e così `(⊕ /out /bin)`, punto più punto. Dagger accetta percorsi assoluti anche dentro una `Directory`, quindi nel piano un percorso è sempre un punto. Il generatore tipa gli argomenti `path` come `Abs`, `address` come `Image`, `args` come `(List Arg)`.

**Le istanze.**

| Dominio | Punti | Spostamenti | Regioni | Stato |
|---|---|---|---|---|
| Percorsi | `/out` | `"hello"` | sottoalberi | fatto, regioni comprese |
| Tempo | `"2026-10-15T10:00:00Z"` | `"1h30m"` | finestre | fatto: `(Affine Instant Duration ≥t)`, finestre come intervalli |
| Indirizzi IP | `"10.0.0.5"` | offset (`Nat`) | blocchi CIDR `"10.0.0.0/24"` | fatto: `Ip.⊕` con overflow escluso, subnet disgiunte |
| Porte | `8080` | — | intervalli | fatto: raffinate, porte non allocate due volte |
| Immagini | — | — | — | fatto, solo raffinamento |

**Precisazioni matematiche.** I percorsi non sono uno spazio affine in senso stretto: senza `..` gli spostamenti formano un monoide, non un gruppo, e per questo la differenza esiste solo se un punto contiene l'altro. Tempo e indirizzi sono invece gruppi veri, ma gli indirizzi vivono modulo 2³², quindi l'overflow va escluso con un raffinamento. Le porte hanno regioni ma non spostamenti. Le immagini non sono affini: hanno solo il raffinamento; la distinzione tra tag e digest è quella tra un punto mobile e un punto fisso, e `pinned?` significa esattamente "fisso".

**Esempio.** Una build Go che esporta il binario. Il binario `bin` è derivato dal punto `out`, quindi il fatto che stia dentro la directory esportata, `(⊑ bin out)`, vale per costruzione:

```
(def go-build : (→ Dir Dir)
  [src] (let [root /src, out /out, bin (/ out "hello")]
          (pipe (container)
                (from "golang:1.25-alpine")
                (with-mounted-cache /go/pkg/mod (cache-volume "go-mod"))
                (with-env "CGO_ENABLED" "0")
                (with-dir root src)
                (with-workdir root)
                (with-exec ["go" "build" "-o" bin "."])
                (dir-of out))))

(def binario-dentro-out : (⊑ (/ /out "hello") /out)
  auto)
```

Scritto con le sole stringhe, `"/out/hello"` nel comando e `"/out"` in `dir-of` ripeterebbero la stessa conoscenza due volte, senza che nulla ne controlli la coerenza. `let` lega in sequenza; le virgole sono spazi; un letterale di punto non può essere catturato da un `let` che lega `root`.

**Il limite.** Gli argomenti di `with-exec` restano in gran parte stringhe: modellare la riga di comando di ogni strumento non è fattibile. Si tipano i valori che vi si interpolano, come `bin` (`Arg` accoglie stringhe e punti), non la sintassi dello strumento. È il confine tra disegno ed esecuzione: la riga di comando è lo scalpello dello scultore.

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

La distinzione di fase viene gratis dai tipi: `(Remote Bool)` non è `Bool`, quindi un'osservazione dentro un `if` è un errore di tipo, e `branch` su un `Bool` pure. Le osservazioni sono un elenco chiuso: `passes?` (exit code 0, dopo `try-exec`, che è `withExec` con `expect: ANY`) e i campi `Boolean` dello schema, come `Directory.exists`. Sopra `passes?` la libreria `files` costruisce le osservazioni sul contenuto dei file: `(includes? f "PASS")` fa girare `grep` in un container fissato per digest, e il programma riceve solo l'esito. Il contenuto non torna mai al linguaggio, e i controlli contano come test per `Before`.

Il runner realizza `branch` chiedendo la condizione e sottomettendo il ramo scelto, nella stessa sessione. A secco stampa un piano per ogni combinazione di esiti, con la condizione che lo sceglie. Poiché entrambi i rami stanno nel piano, una proprietà del piano va provata su tutti e due: è l'analisi statica dei funtori applicativi selettivi (Mokhov e altri, 2019).

## Effetti in sequenza (proposta)

Proposta, non ancora implementata. È il passo che serve alle librerie per il cloud e per gli strumenti DevOps (AWS, Azure, Kubernetes): una pipeline vera fa più cose in ordine, e alcune agiscono sul mondo.

**Il problema.** Oggi un piano ha un'uscita sola, in cima: `overlay`, `replace` o `publish`. Un deploy si può scrivere solo come `with-exec` dentro un container, e lì è un effetto nascosto:
- Dagger lo mette in cache, quindi la seconda esecuzione non rifà il deploy;
- `effects` e `Before` non lo vedono, quindi «niente deploy senza test» non si può provare;
- nessuna regola dice in che ordine avvengono il deploy e l'export.

**Quattro costruttori del nucleo**, accanto a `branch`, `overlay`, `replace` e `publish`. Sono uscite, cioè `(Export Dir)`, e stanno nell'elenco degli snodi di `gen.ss`:

| Costruttore | Tipo | Che cosa fa |
|---|---|---|
| `(apply c cmd)` | `(→ Container (List Arg) (Export Dir))` | esegue `cmd` in `c` come effetto: la preparazione di `c` resta in cache, `cmd` no |
| `(then a b)` | `(→ (Export Dir) (Export Dir) (Export Dir))` | realizza `a`, poi `b`; se `a` fallisce, `b` non avviene |
| `skip` | `(Export Dir)` | l'uscita che non fa niente, per i rami di un `branch` |
| `(probe c cmd)` | `(→ Container (List Arg) (Remote Bool))` | un'osservazione del mondo, non in cache: «lo staging risponde?» |

**Semantica.**
- **L'ordine** è quello di `then`: da sinistra a destra, e ci si ferma al primo fallimento. Dentro ogni uscita Dagger resta pigro e parallelo come oggi.
- **Le osservazioni si fanno quando le si raggiunge.** Un `branch` dentro il secondo argomento di `then` si risolve dopo che il primo è stato realizzato, quindi un `probe` vede il mondo dopo il deploy in staging. Il piano resta statico: entrambi i rami ci sono, e `disegno plan` stampa una sequenza di uscite per ogni combinazione di esiti.
- **La cache.** Il runner aggiunge `withEnvVariable(DISEGNO_RUN, <id dell'esecuzione>)` subito prima del comando di `apply` e di `probe`. Così si rifà solo l'effetto, non la costruzione dell'ambiente. `passes?` resta in cache, perché osserva il risultato di un input, non il mondo.
- **Il resoconto.** Una voce che contiene un `apply` lo dice: «effetto», con il comando. Le voci successive a un effetto fallito compaiono tra quelle non realizzate.

**Le proprietà.** `effects` impara a seguire `then`. Ogni uscita porta con sé le osservazioni che la proteggono e le uscite che la precedono. Così, oltre a `Before`, si scrive l'ordine:

```
(def rilascio : (→ [src (Host ".")] (Export Dir))
  [src] (branch (passes? (test src))
          (then (publish (image src) "registry.example.com/app:1")
                (then (apply (kubectl staging) ["kubectl" "apply" "-f" "/k8s"])
                      (branch (probe (curl) ["curl" "-fsS" "https://staging.example.com/health"])
                        (apply (kubectl prod) ["kubectl" "apply" "-f" "/k8s"])
                        skip)))
          (overlay "reports" (report src))))

(def test-prima-del-deploy : (→ [src Dir] (Before test? apply? (rilascio src))) [src] auto)
(def prod-dopo-staging : (→ [src Dir] (Precedes staging? prod? (rilascio src))) [src] auto)
```

`Precedes` dice che ogni effetto che soddisfa `prod?` ha davanti, nella sua sequenza, un effetto che soddisfa `staging?`. Come `Before`, vale per ogni sorgente, perché `effects` non scende nelle directory.

**Perché `then` è binario.** Una sequenza `(sequence [a b c])` sarebbe più comoda, ma un costruttore di `Obj` con un argomento `(List (Obj k))` è un induttivo annidato, e la positività lo rifiuta. Il binario con `skip` basta, ed è un monoide: le librerie possono offrire una forma più comoda come `def`.

**Che cosa non si fa, per ora.**
- uscite in parallelo: Dagger parallelizza già dentro ogni uscita;
- compensazioni e rollback: un `(otherwise a b)`, che realizza `b` se `a` fallisce, si aggiungerebbe allo stesso modo;
- attese e tentativi ripetuti, come «aspetta che lo staging sia pronto»: un `probe` con un numero massimo di tentativi resterebbe totale, ma va deciso dove sta il conteggio.

**Il passo dopo: i segreti.** Un `apply` verso il cloud vuole credenziali. Il modello è quello di `Host`: `main` dichiara nella firma `(Secret "AWS_SECRET_ACCESS_KEY")`, il runner lo legge con `secret(uri: "env://AWS_SECRET_ACCESS_KEY")` e lo passa con `withSecretVariable`. Il valore non torna al linguaggio e non compare nel piano stampato. Serve aggiungere `Secret` ai tipi del generatore.

**Da decidere.**
1. `apply` con l'ambiente e il comando separati, così la preparazione resta in cache. In alternativa, `(apply c)` sull'ultimo `with-exec` di `c`: si scrive meno, ma è meno chiaro che cosa sia l'effetto.
2. Se un `probe` conta come test per `Before`, come i controlli sul contenuto. La proposta è di sì: «deploy in prod solo se lo staging risponde» è un test sul mondo.

## Nucleo fidato

La parte sporca è piccola, chiusa e scritta da chi progetta il linguaggio.

- **Kernel** (fidato): ricontrolla ogni termine prodotto dall'elaboratore, con `Type n : Type n+1`, mai `Type : Type`. L'elaboratore (nomi, impliciti, metavariabili, pattern) può sbagliare; il kernel no.
- **Snodi**: elenco chiuso di costruttori del nucleo che il runner realizza in modo speciale: `%host-dir`, `try-exec`, `passes?`, `branch`, `overlay`, `replace`, `publish`, `cache-volume`. Il cache volume è l'unico stato che persiste tra un'esecuzione e l'altra e non è indirizzato per contenuto: finché si usa come cache non tocca il disegno, ma è dichiarato qui invece di restare implicito tra i campi generati.
- **`extern`** è rimasto solo per i tipi opachi e le primitive pure, che calcolano soltanto sui letterali: `String`, `contains?`, `image-ref?`, `segment?`, `distinct?`, e per comporre testo `concat`, `show`, `show-ip`, così una configurazione si rende dagli stessi valori su cui valgono i teoremi. Un extern non mente: restituisce un tipo opaco o calcola; mai una proposizione, mai un dato del mondo.
- **Runner**: l'unico posto dove si ammette il non determinismo. Realizza `branch`, `Host` ed `Export`.
- **Builtin**: il nucleo non nomina la libreria. Conosce un elenco chiuso di chiavi (`nat`, `zero`, `suc`, `list`, `string`, `abs`, `ip`, `obj`, `host`, …) e la libreria lega ciascuna a un suo nome con `(builtin chiave nome)`, come i `BUILTIN` di Agda. Passano da qui i letterali (`0`, `"x"`, `/out`, `[a b]`, `"10.0.0.0/8"`), le prove di `auto` (`⊤`, `≡`, `⊥`), l'accelerazione, il piano e l'input di `main`. È fidato come `extern`: si controlla che il nome esista e sia del genere giusto (tipo, costruttore, definizione), non che abbia la forma attesa.
- **Numerali nativi** (come in Lean): nella logica `Nat` è `zero`/`add1`, nel valutatore un numero è un intero; le definizioni legate alle chiavi `plus`, `monus`, `times`, `leq?`, `lt?`, `nat-eq?`, `pow2` (nel prelude `+`, `∸`, `*`, `≤?`, `<?`, `nat=?`, `pow2`) si calcolano nativamente sui numeri. È una scorciatoia fidata: `test.ss` verifica che coincida con le clausole unarie, e una mutazione viene presa.
- **Copertura**: un caso che nessuna clausola prende è coperto se una sua variabile, divisa, dà solo casi impossibili (l'assurdo implicito).
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
| Niente scappatoie | niente postulati: una `def` deve avere un corpo, o un pattern assurdo verificato; `extern` solo nella libreria standard | `(def postulato : ⊥)`, `(def f : (¬ (≡ 0 0)) [()])` |
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

**Regioni e montaggi disgiunti.** Una regione di percorsi è il sottoalbero di un punto. `(⋔ p q)` dice che due sottoalberi sono disgiunti, perché i percorsi si separano a un passo; è induttivo come `⊑`, e `auto` trova il punto di separazione (serve solo la primitiva `distinct?` sui segmenti letterali). I montaggi si raccolgono lungo la catena di un container (`chain`, generato: segue `self` e non scende negli argomenti), perché due container diversi non si contendono il file system. Così la garanzia vale per ogni sorgente:

```
(def montaggi-disgiunti : (→ [src Dir] (Disjoint-mounts (go-build src)))
  [src] auto)
```

**I controlli come teoremi.** `checks.disegno` raccoglie le leggi della libreria standard e le garanzie sui piani: associatività di `+` e `++`, transitività di `⊑`, la legge affine tramite l'istanza, la lettura dei letterali, `pinned`, `Before`, i montaggi. Le leggi generali sono dimostrate per induzione, i casi concreti calcolati da `auto`. Il file si verifica a ogni esecuzione dei test (o da solo: `disegno check tests/checks.disegno`). È la protezione dalle rotture: una prova di mutazione che rompe `++`, `⊖`, `⊑-step` o la raccolta dei montaggi fa fallire il controllo, con l'errore di tipo che indica la legge violata. Anche ciò che **non** deve valere è un teorema, grazie alla negazione.

**Negazione e pattern assurdi.** `(¬ A)` è `(→ A ⊥)`. Un pattern assurdo `()` dichiara che a quella posizione non c'è alcun valore, e la clausola non ha corpo:

```
(def fuori-a-mano : (¬ (⊑ /out /src))
  [(⊑-step ())])                       ; servirebbe una prova di (⊑ root /src): impossibile
```

Il checker verifica `()` dopo aver unificato tutti i pattern della clausola: ogni costruttore deve essere in conflitto con gli indici, altrimenti `() non è assurdo`. Su proposizioni chiuse `auto` trova da solo l'albero degli assurdi e lo fa verificare come definizione ausiliaria: `(def annidati-non-disgiunti : (¬ (⋔ /src /src/cache)) auto)`. Così `checks.disegno` contiene anche le garanzie negative (immagine non pinnata, montaggi sovrapposti), e una mutazione che rende `⋔` troppo permissiva viene presa da un teorema. In `test.ss` restano i rifiuti del checker stesso: nomi riservati, errori di tipo, e il fatto che `()` non sia una scappatoia (`(¬ (≡ 0 0))` con `[()]` è rifiutato).

**Tempo, indirizzi, porte.** Tutte e tre le istanze poggiano sui naturali, la cui legge `q + (p ∸ q) = p` è dimostrata una volta per induzione sull'ordine induttivo `≤`. Il tempo è un'istanza `Affine` vera, con l'ordine decidibile `(So (≤? q p))`: sugli istanti, miliardi di secondi, una prova induttiva sarebbe lunga quanto il numero, e il lemma di riflessione `≤-from` collega le due forme. Le regioni su una retta sono intervalli semiaperti: finestre di tempo, blocchi CIDR, intervalli di porte. I letterali li leggono lettori del nucleo (`"1h30m"`, `"2026-10-15T10:00:00Z"`, `"10.0.0.0/24"`); un blocco CIDR non allineato, un'ora 25 o la porta 70000 sono errori di tipo.

```
(def subnet-disgiunte : (Disjoint-subnets ["10.0.0.0/24" "10.0.1.0/24" "10.1.0.0/16"])
  auto)

(def porte-doppie : (¬ (Distinct-ports (pipe (container) (with-exposed-port 8080) (with-exposed-port 8080))))
  auto)
```

**Quando una prova non c'è.** Gli errori portano la posizione, `file:riga:colonna`, dell'espressione più vicina: il reader conserva le posizioni (la trasformazione delle quadre non cambia le lunghezze), e il driver li stampa su stderr nel formato dei compilatori. Quando `auto` fallisce su una congiunzione dice quale parte non vale: per questo i predicati che si compongono (`Holds`, `Apart`, `Cidr-apart`, `port≠`) sono induttivi e non `(So …)`, che si ridurrebbe subito a `⊥` perdendo i suoi argomenti.

```
cookbook/05-network.disegno:25:1: auto: nessuna prova di (Cidr-apart "10.0.1.0/24" "10.0.1.128/25")
```

**Cosa resta empirico**
: che i test passino o che il binario funzioni sono osservazioni, non proposizioni. Gli unit test del codice dentro i container restano e li esegue Dagger.

## Runtime e ospite

Dagger è la piattaforma, come la BEAM per Gleam. L'ospite è Chez Scheme 10. Il linguaggio non è un SDK Dagger: il runner è un client di una sessione.

- **Sessione**: `dagger api with-session` (Dagger 1.0) mette `DAGGER_SESSION_PORT` e `DAGGER_SESSION_TOKEN` nell'ambiente; il motore si sceglie con `DAGGER_ENGINE`.
- **Trasporto**: POST su `http://127.0.0.1:$DAGGER_SESSION_PORT/query`, token come utente basic auth. Il client HTTP è scritto a mano (FFI su `socket`/`connect` di libc, HTTP/1.0 senza TLS su localhost), con un parser JSON minimo: poco codice, nel nucleo.
- **Richieste**: una catena è un documento GraphQL e parte in una richiesta. **Correzione al documento originale**: quando un oggetto è argomento di un altro (una Dir passata a `withDirectory`), non può stare nella stessa query, perché GraphQL non accetta una selezione come argomento. Il runner chiede prima il suo `id` e poi lo passa. Il piano resta statico; le richieste non sono sempre una sola.
- **Ordine**: le richieste partono in ordine deterministico, da sinistra a destra.

Perché Chez: nella tesi "tutto su Dagger" l'ecosistema dell'ospite non conta; serve un substrato minimale per un evaluator nostro (NbE, elaborazione, piano). Racket gira su Chez, quindi Chez toglie uno strato; Idris 2 compila verso Chez.

Precedente sul lato Dagger: Dang, il linguaggio nativo di Dagger 1.0, conferma che un linguaggio il cui runtime è Dagger è percorribile. Disegno si colloca come un Dang con Martin-Löf, totalità e piano ispezionabile.

## Architettura

```
README.md  DESIGN.md  ARCHITECTURE.md  flake.nix
src/       core.ss  types.ss  plan.ss  main.ss  lsp.ss   il nucleo, il driver, il server LSP
lib/       prelude  text  affine  paths  time  net  dagger  engine  files    la libreria standard, in moduli (engine è generato)
tools/     gen.ss                                    il generatore dallo schema
tests/     test.ss  checks.disegno                   i test e i teoremi di controllo
cookbook/  00-basics … 06-theorems  hello/            le ricette
editors/   tree-sitter-disegno/  nvim/              la grammatica e il plugin per Neovim
```

| File | Ruolo |
|---|---|
| `src/core.ss` | nucleo: stampa GraphQL, HTTP su socket, JSON, sessione |
| `src/types.ss` | elaboratore e kernel: NbE, unificazione, pattern, copertura, terminazione, positività, `record`, `auto`, letterali, numerali nativi |
| `src/plan.ss` | runner: dal piano (dato) al GraphQL, `branch`, esecuzione e piani a secco |
| `src/main.ss` | driver: `check`, `plan`, `run`, `lsp`, `type`; trova la radice dalla propria posizione |
| `src/lsp.ss` | il server LSP: JSON-RPC su stdin/stdout, diagnostica da un controllo in un processo a sé |
| `editors/` | la grammatica tree-sitter con le query, e il plugin per Neovim (filetype, tree-sitter, LSP, `:make`) |
| `lib/prelude.disegno` | la logica, sempre caricata: uguaglianza, `⊥`, `⊤`, `Bool`, `So`, `Nat`, `≤`, liste, `Σ`, `Either`, `Every`, `Pairwise`; niente extern |
| `lib/text`, `affine`, `paths`, `time`, `net` | stringhe; spazi affini e intervalli; percorsi e regioni; istanti e durate; IP, CIDR e porte |
| `lib/dagger.disegno` | il piano: `Image`, `Arg`, `engine`, `Host`, `Export`, nomi corti, proprietà del piano |
| `lib/files.disegno` | i file: `file`, `put-file`, `merge`; che cosa scrive una directory (`Disjoint-writes`, `Writes-within`); osservazioni sul contenuto guardate da Dagger (`includes?`, `matches?`, `empty?`, `same-content?`) |
| `lib/engine.disegno` | generato: `Kind`, `Obj`, alias, `nodes`, `chain` |
| `tools/gen.ss` | generatore di `lib/engine.disegno` dallo schema (sotto `dagger api with-session`) |
| `tests/test.ss` | test: nucleo, tipi, rifiuti, accelerazione, piani a secco e, sotto `dagger api with-session`, dal vivo |
| `tests/checks.disegno` | le leggi e le garanzie come teoremi, verificate a ogni test |
| `cookbook/` | sette ricette numerate e commentate, verificate dai test (`check`, e `plan` se hanno un main); `hello/` è il sorgente Go degli esempi |
| `flake.nix` | il pacchetto `disegno` (`nix run`), la shell, il motore dedicato con le CA dell'host |

**Uso.** `nix run . -- check|plan|run prog.disegno`, oppure `disegno …` nella shell `nix develop`; `disegno lsp` è il server per gli editor. nixpkgs è fissato a `nixos-25.11`. `run` apre da sé la sessione con `dagger api with-session`. I percorsi relativi di `Host` ed `Export` si risolvono rispetto alla cartella del programma, così un programma si lancia da qualunque cartella. Il motore Dagger gira in un container dedicato (`disegno-engine`) che monta il bundle CA dell'host, per attraversare un proxy TLS aziendale; il motore passa le CA anche ai container che esegue.

## Limitazioni accettate

In cambio della purezza e della semplicità:

- niente ricorsione generale e niente IO diretto;
- niente piano dinamico: i dati del mondo non tornano mai al linguaggio;
- snodi chiusi: l'utente non estende né gli extern né i costruttori del nucleo;
- librerie curate: le integrazioni (file, e poi cloud e strumenti DevOps) sono moduli di `lib/` scritti e mantenuti nel repo, con uno scope che cresce nel tempo, come i pacchetti ufficiali di Elm; non si importano librerie esterne. Limita, ma tiene il controllo su ciò che un programma può dichiarare;
- la totalità vale per la descrizione, non per l'esecuzione: un comando in container può restare non deterministico;
- ciò che non passa da Dagger è di seconda classe, raggiungibile solo tramite comandi in container;
- assioma K: il pattern matching unifica `x = x`;
- un tipo che non si ricava è `Type₀`; niente polimorfismo di universo né cumulatività (`Nat : Type 1` è rifiutato, quindi `(≡ Nat Nat)` non si scrive);
- terminazione con un solo argomento decrescente fisso (Ackermann è rifiutato);
- solo gli argomenti obbligatori dei campi del motore; i tipi del motore sono un elenco consentito;
- l'argomento di `Remote` ed `Export` è per ora documentazione: esistono solo osservazioni booleane ed export di directory;
- `auto` calcola su dati concreti e cerca prove componendo costruttori, in profondità limitata e solo su obiettivi senza metavariabili; un exit code vale vero se è 0 (convenzione nel runner).

## Questioni aperte

- [x] Quale primitiva usa un client per leggere l'host: `host.directory`, in Dagger 0.21 come nella 1.0 (beta.18). Workspace della 1.0 serve ai moduli, non a un client.
- [ ] Export o Changeset per scrivere. Oggi export classico (`overlay`, `replace` con `wipe`).
- [ ] Il Changeset rappresenta anche le cancellazioni? Deciderebbe se servono ancora due costruttori di export.
- [x] Quali osservazioni ammettere e come tiparle: elenco chiuso, `(Obj Kind.bool)`. Resta da tipare osservazioni non booleane, con un `Kind` indicizzato.
- [x] Tipi raffinati per immagini (tag e digest) e percorsi; struttura `Affine` con la legge dimostrata per i percorsi.
- [x] Regioni dei percorsi: contenimento, disgiunzione, montaggi disgiunti come teorema sul piano.
- [x] Le altre istanze: naturali (`(Affine Nat Nat ≥N)`), tempo, indirizzi IP con blocchi CIDR, porte; regioni come intervalli.
- [ ] La legge affine degli indirizzi: `Ip.⊕` chiede la prova di non overflow, quindi non è il + totale del record `Affine`; la legge segue da quella dei naturali più l'irrilevanza delle prove di `So`.
- [x] Negazione nei teoremi: `¬`, pattern assurdi `()`, refutazione con `auto`.
- [ ] IaC: come recuperare tipi utili quando l'infrastruttura passa da comandi in container.
- [x] Proprietà d'ordine, come `test-prima-di-publish`: `publish` è un'uscita del piano, `Before` si prova per ogni input.
- [ ] Effetti in sequenza (`apply`, `then`, `skip`, `probe`) e segreti come input di `main`: proposta nella sezione «Effetti in sequenza».
- [ ] Teoremi generali sui piani (`pin-corretto`): principio d'induzione generato per `Obj`, o lemmi sopra `nodes`.
- [x] Errori con file:riga:colonna (formato dei compilatori, letto da `:make` e dalla quickfix di Neovim) e messaggi di `auto` che indicano la parte che non vale: `nessuna prova di (Cidr-apart "10.0.1.0/24" "10.0.1.128/25")`.
- [x] Passaggio a Dagger 1.0 (beta.18): il flake scarica il binario da dl.dagger.io, `dagger api with-session` e `DAGGER_ENGINE`. Nessun cambio nel runner; nello schema `GitRepository.latest-version` diventa `latest`, `commit` restituisce `GitCommit` (escluso), nuovi `with-run`, `with-shell`, `GitRef.contains`. Da tornare a github:dagger/nix quando esce la 1.0.

### Da fare

- **Libreria in moduli**: fatti `import` e i builtin. Il prelude da solo è la teoria di Martin-Löf, e i capitoli 1–4 del libro si controllano solo con quello; il nucleo conosce la libreria solo attraverso le chiavi builtin. Restano nel nucleo, come contratto con il generatore, i nomi generati (`Kind.*`, gli snodi, `Container.with-exec` per le voci) e, solo per la stampa, gli alias `(Remote Bool)` ed `(Export Dir)`. Si può aggiungere: dire in quale modulo sta un nome sconosciuto.
- **Editor**: fatti tree-sitter (grammatica, evidenziazione) e l'LSP in Chez (`disegno lsp`): diagnostica mentre si scrive con tutti gli errori del file (un errore non ferma il controllo; i "nome sconosciuto" a cascata si tacciono), hover con il tipo dei nomi globali e le varianti dei nomi corti, vai alla definizione anche dentro la libreria, simboli del file; con il plugin `nvim-disegno`. Restano hover e definizione delle variabili locali (il reader non conserva la posizione degli atomi) e il completamento.
- **Pointless Disegno** (`book/`): un libricino per imparare i tipi dipendenti, sul filo di Gentzen, Dummett e Prawitz (il significato nelle introduzioni, l'eliminazione in armonia). Scritti i nove capitoli, dalle introduzioni alle prove come programmi, al livello di Pie (λ, `the`, impliciti, Σ, `Either`, `transport`). Le soluzioni degli esercizi sono in `book/solutions/`, verificate dai test.
- **I log: il resoconto dell'opera rispetto al disegno.** Il log di Dagger racconta il meccanismo (le chiamate, la cache) o l'output grezzo, e chi legge annega nella preparazione dell'ambiente. In Disegno il piano è noto prima di eseguire, con i nomi del programma e le proprietà già dimostrate: il log dice solo il residuo, ciò che si impara eseguendo. In CI (o senza terminale) `disegno run` non mostra la TUI e stampa una riga per **voce**: una definizione del programma che costruisce un pezzo di piano (`chez`, `test`, `pubblica`), con esito, che cosa ha fatto e tempo. Un passo appartiene alla voce nel cui corpo è stato costruito (mentre la valutazione apre il corpo di una voce, i `with-exec` ne prendono il nome; gli argomenti li ha valutati il chiamante); i passi di `main` sono di `main`. Una voce i cui passi non dipendono da un input del programma (un `Host`) è **ambiente**, e si dice soltanto «ambiente»; altrimenti la riga mostra il comando di lavoro. Le osservazioni (`passes?`, `exists?`) dicono la risposta e quindi il ramo. In fondo, «realizzato» e che cosa è stato esportato o pubblicato. L'output dei comandi è la **prova**: in CI sta nel gruppo chiuso della voce, altrove non si stampa; una voce fallita mostra le ultime righe del passo, la posizione del suo `with-exec` nel sorgente (anche nel terminale, e su GitHub un'annotazione), e le voci non realizzate.
  La prova viene dal flusso dei log del motore (`/v1/logs` della sessione, server-sent events con record OpenTelemetry in JSON), letto in un thread mentre il passo gira; il passo finisce quando il comando chiude stdout e stderr (`stdio.eof`). Il motore consegna stdout e stderr a pacchetti separati: le righe aspettano 300 ms dal loro arrivo (orologio locale) ed escono nell'ordine dell'istante del motore, senza mai confrontare i due orologi; righe scritte nello stesso millisecondo restano in ordine incerto, come in ogni strumento che legge due pipe. Un passo in cache non esegue niente: la prova è `combinedOutput`. Dagger è pigro e ha la cache, quindi eseguire passo per passo non rifà il lavoro.
  Restano: dire «già realizzato» per le voci in cache (probabilmente dalle tracce, `/v1/traces`), la prova conservata come file per voce, e il resoconto come dato di Disegno, da confrontare tra run.

## Fonti

- G. Vasari, *Le vite de' più eccellenti pittori, scultori e architettori*, 1568, Introduzione, Della pittura, cap. XV "Che cosa sia disegno" ([Wikisource](https://it.wikisource.org/wiki/Le_vite_de%27_pi%C3%B9_eccellenti_pittori,_scultori_e_architettori_(1568)/Capitolo_15))
- F. Zuccari, *L'idea de' pittori, scultori et architetti*, Torino, 1607

- Client libraries e GraphQL diretto, Dagger
- Endpoint HTTP della sessione
- Dang SDK, Dagger 1.0-beta
- Tipi dell'API Dagger: accesso all'host
- Export di artefatti verso l'host
- A. Kovács, elaboration-zoo (elaborazione con NbE e metavariabili)
- A. Mokhov, G. Lukyanov, S. Marlow, J. Dimino, *Selective Applicative Functors*, 2019
