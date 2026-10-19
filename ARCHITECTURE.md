# Architettura di Disegno: le scelte del linguaggio

Questo documento raccoglie le scelte che danno forma al linguaggio e le loro ragioni. Per ogni scelta dice che cosa si è deciso, perché, che cosa si è scartato e quanto costa. Lo stato del lavoro, gli esempi completi e le questioni aperte stanno in [DESIGN.md](DESIGN.md); qui conta il perché.

Il criterio che regge tutte le scelte è uno solo: **semplicità sopra generalità, consistenza non negoziabile**. Un limite si accetta volentieri se semplifica, purché non apra una falla logica.

## La forma d'insieme

```
sorgente .disegno
  │  reader: s-espressioni; le quadre diventano (%br …); ogni lista ricorda file e offset
  ▼
elaboratore (non fidato)      nomi, impliciti, metavariabili, nomi corti, letterali, pattern, auto
  │  termine del nucleo
  ▼
kernel (fidato)               ricontrolla ogni termine: Π, Type n, globali, letterali
  │
  ▼
valutatore (NbE)              main si riduce a un valore: il piano, un dato induttivo
  │
  ▼
runner (fidato)               dal piano al GraphQL; realizza branch, Host ed Export
  │
  ▼
Dagger                        l'unico che esegue
```

Gli strati, dal più fidato al meno:

| Strato | Dove | Chi lo scrive | Può dichiarare |
|---|---|---|---|
| Nucleo | `src/` | chi progetta il linguaggio | tutto, compresi i nomi `%…` |
| Libreria standard | `lib/*.disegno` | chi progetta il linguaggio | `extern`, `builtin`, `import` |
| Programma | ogni altro file | l'utente | `def`, `data`, `record`, `import` |

## 1. La teoria: Martin-Löf intensionale, con l'assioma K

**Scelta.** Il linguaggio è una teoria dei tipi di Martin-Löf minimale: Π con η per le funzioni, una gerarchia di universi `Type n : Type n+1` e famiglie induttive. Tutto il resto, cioè Σ, `≡`, `⊥`, `⊤`, `Bool`, `Nat` e `List`, è un `data` del prelude.

**Perché.** È il nucleo più piccolo che basta a fare matematica costruttiva e a enunciare proprietà dei programmi. La completezza è verificata, non presunta:
- gli eliminatori dipendenti (`ind-Nat`, `J`, `ind-Σ`, `ind-List`, `ind-⊥`) si scrivono col pattern matching;
- i W-tipi passano il controllo di positività;
- l'eliminazione verso `Type` è ammessa;
- `Type : Type`, i tipi non positivi, la ricorsione non strutturale e i casi mancanti sono rifiutati.

**K.** Il pattern matching unifica `x = x`. Quindi l'unicità delle prove d'identità è dimostrabile, e lo è anche K: `(def k … [P p refl] p)` passa il controllo. È la scelta di Agda senza `--without-K` e di Idris. Rende semplice il matching dipendente: non serve controllare che l'unificazione non usi K. Il prezzo è l'incompatibilità con l'univalenza, che in un linguaggio per CI/CD non serve.

**Scartato.** La teoria dei tipi omotopica (HoTT) e la teoria cubica: aggiungono complessità che non ripaga in questo dominio. L'uguaglianza estensionale: renderebbe indecidibile il controllo dei tipi.

## 2. Il kernel conosce solo Π e Type

**Scelta.** Il kernel (`k-infer`, `k-check`) conosce variabili, globali, applicazioni, λ, Π, `Type n`, annotazioni e i letterali di stringa e di numero. Non sa che cosa siano `≡` o `Nat`: per lui sono globali con un tipo. La conversione è la stessa unificazione dell'elaboratore, usata senza metavariabili.

**Perché.** È il criterio di de Bruijn: un controllore piccolo che chiunque può rileggere. L'elaboratore può sbagliare a ricostruire un implicito, il kernel no. Se ne è avuta una prova durante la verifica: un caso in cui l'elaboratore lasciava passare un termine mal tipato, `(def e : (≡ Nat Nat) refl)`, è stato fermato dal kernel.

**Costo.** Nel kernel non entrano il pattern matching, la copertura e la terminazione, che si controllano nell'elaboratore. Rientrano quindi nella base fidata insieme al kernel, e per questo ciascuna ha i suoi test di rifiuto.

## 3. Pattern matching dipendente invece degli eliminatori

**Scelta.** Una sola forma di definizione: `def nome : tipo` seguito da clausole `[pattern] corpo`. Valgono queste regole:
- la copertura si controlla dividendo i casi, con i tipi;
- un caso è assurdo implicitamente se gli indici sono inconciliabili;
- `()` dichiara un assurdo esplicito, che il checker verifica;
- la terminazione è strutturale, su un argomento fisso.

**Perché.** Le prove scritte per casi si leggono come le dimostrazioni sulla carta, mentre gli eliminatori sono illeggibili oltre i casi semplici. Poiché gli eliminatori si derivano dal pattern matching, la teoria non perde nulla.

**Costo.** Un solo argomento decrescente: Ackermann è rifiutato. Non ci sono definizioni mutue né induttivi annidati: `Rose` con `(List Rose)` è rifiutato, perché la positività non attraversa i parametri. Si aggiungono il giorno in cui servono; per ora si codificano con famiglie indicizzate, come si fa già per il piano (sezione 7).

## 4. Universi stratificati, senza cumulatività

**Scelta.** `Type n : Type n+1` e mai `Type : Type`. Non c'è polimorfismo di universo né cumulatività. Un tipo che non si ricava è `Type₀`.

**Perché.** I programmi di CI/CD vivono quasi interamente in `Type₀`. Ogni meccanismo di universo in più, cioè variabili di livello, vincoli e cumulatività, complica l'elaboratore e il kernel per un uso che qui non c'è.

**Costo.** `Nat : Type 1` è rifiutato: non si scrive `(≡ Nat Nat)` e non si fa una lista di tipi. Se servirà, il primo passo è la cumulatività, che tocca solo il confronto dei livelli nel kernel.

## 5. Elaborazione: NbE, metavariabili, impliciti

**Scelta.** L'elaboratore segue lo stile di Kovács nell'elaboration-zoo:
- termini con indici di de Bruijn, valori con livelli, normalizzazione per valutazione;
- metavariabili risolte con l'unificazione a pattern di Miller;
- gli argomenti impliciti si inseriscono da sé;
- nelle firme si quantificano da sé le variabili libere, ma solo i **nomi da variabile**, cioè una lettera ed eventualmente delle cifre (`A`, `x`, `n2`).

**Perché.** NbE dà la conversione per calcolo senza scrivere a mano la sostituzione, ed è la tecnica più semplice tra quelle corrette. La regola dei nomi da variabile serve a far emergere gli errori: un `Port` sconosciuto, magari per un `import` dimenticato, è un errore e non diventa un tipo qualsiasi che produce messaggi incomprensibili tre righe dopo.

**Scartato.** Gli impliciti dichiarati a mano (`variable` di Agda, `{A : Type}` ovunque): rumore in ogni firma della libreria.

## 6. Totalità e niente IO: il programma è un piano

**Scelta.** Non c'è ricorsione generale né IO. `main` si riduce a un valore, il piano, che è un dato induttivo; il runner lo interpreta. I dati del mondo non tornano mai al linguaggio.

**Perché.** È ciò che rende sensati i teoremi: il programma termina per costruzione e il piano è noto per intero prima di eseguire, quindi le proprietà del piano si provano. È l'IO a richieste e risposte di Haskell 1.0, la derivazione di Nix e il Cmd di Elm, senza l'evaluation in fase di build di Nix (*import from derivation*).

**Due tempi.**
- `if` decide su valori noti, mentre si costruisce il piano, ed è una `def` del prelude.
- `branch` decide su osservazioni durante l'esecuzione, ed è un costruttore del piano che contiene entrambi i rami.
- `(Remote Bool)` non è `Bool`: la distinzione di fase la fanno i tipi.
- Il contenuto di un file non torna al linguaggio. `includes?`, `matches?`, `empty?` e `same-content?` (modulo `files`) sono osservazioni che Dagger calcola in un container, come `passes?`; al runner arriva un exit code, al programma un `(Remote Bool)`. Per `Before` contano come test.

È l'analisi statica dei funtori applicativi selettivi (Mokhov e altri, 2019).

**Un'osservazione non è un assioma.** L'esito di un'osservazione è vero per quell'esecuzione e decide il ramo, ma non entra mai nella logica. È garantito per costruzione:
- non esiste una funzione da `(Remote Bool)` a `Bool` o a `Type`;
- l'unico modo di usare un'osservazione è `branch`, che è un costruttore del piano, cioè un dato;
- il pattern matching su `(passes? c)`, come fa `test?`, guarda quale osservazione è, non che cosa risponde.

Un teorema parla quindi solo della forma del piano: «il test viene prima di prod» è vero e si dimostra. Che il test abbia risposto sì è la verità di quel test, in quel momento, non del mondo: lo staging ha risposto, non è detto che sia sano.

**Effetti in sequenza.** Le uscite del piano si compongono: `(then a b)` realizza `a` e poi `b`, `skip` non fa niente, `(apply c cmd)` esegue un comando come effetto, fuori dalla cache, e `(probe c cmd)` osserva il mondo quando lo si raggiunge. Le proprietà d'ordine seguono il piano come una storia di osservazioni e uscite: `Before` («nessun deploy senza test») e `Precedes` («prod dopo staging») si provano per ogni sorgente.

**Segreti.** Le credenziali entrano come gli input: `(Host-secret "AWS_ACCESS_KEY_ID")` nella firma di `main`, letto da una variabile d'ambiente. Il valore non torna al linguaggio e non compare nel piano, che nomina solo la variabile; un programma non può creare un segreto da sé né leggerne il testo.

**Costo.** Niente piano dinamico: ciò che dipende da un risultato si esprime con `branch` su un'osservazione, non con un valore che torna indietro.

## 7. Il piano generato dallo schema

**Scelta.** Le operazioni del motore sono costruttori di una famiglia sola, `(data Obj : (→ Kind Type) …)`, generata da `tools/gen.ss` per introspezione dello schema di Dagger. Il nome del costruttore è il campo (`Container.with-exec`), i binder sono gli argomenti. Il generatore produce anche `nodes` e `chain`, l'attraversamento con cui le proprietà si scrivono in poche righe.

**Perché.** Con un indice non servono tipi mutuamente ricorsivi (`Container`, `Directory` e `File` si richiamano a vicenda), e positività, copertura e universi funzionano senza casi speciali. Un piano opaco, fatto di primitive extern, non si potrebbe ispezionare: l'utente ha ritenuto necessario che il piano fosse un dato.

**Costo.** Il generatore è nella base fidata e i nomi che genera sono un contratto con il nucleo: `Kind.*`, gli snodi e `Container.with-exec` per i log. Si prendono gli argomenti obbligatori, più quelli opzionali che una tabella promuove campo per campo (`include` ed `exclude` di `filter`, `permissions` di `with-new-file`, `useEntrypoint` di `as-service`), e un elenco consentito di tipi.

**I service.** Un service di Dagger (un database, un emulatore come LocalStack) è un valore del piano come un container: `as-service` lo ricava da un container, `with-service-binding` lo lega a un altro sotto un nome. Dagger lo avvia quando un comando legato a lui gira, aspetta che le porte esposte rispondano, lo tiene per tutta la sessione e lo ferma alla fine. Non serve un effetto: la vita del service la decide il motore.

## 8. Letterali secondo il tipo: i punti non si sommano

**Scelta.** Un letterale si legge secondo il tipo atteso:
- `"golang:1.25-alpine"` è un `Image`, `/out` è un punto, `"1h30m"` una durata, `"10.0.0.0/24"` un blocco CIDR;
- un tipo raffinato è un record con un valore e la sua prova, e l'elaboratore ha una regola sola per accoglierlo: un costruttore il cui primo campo prende il valore e i cui campi restanti sono proposizioni fa da coercizione, con le prove calcolate da `auto`;
- posizioni e spostamenti formano spazi affini (`Affine`), e le relazioni come `⊑` o `⋔` sono induttive.

**Perché.** Nel codice di CI quasi tutto è una stringa, e le stringhe nascondono la distinzione tra posizioni e spostamenti. Con le relazioni induttive le leggi si dimostrano per induzione senza confrontare stringhe e senza postulati.

**Costo.** I lettori dei formati, cioè durate, istanti, IP e CIDR, sono codice del nucleo. Restituiscono solo i campi; il costruttore lo prende dal tipo.

## 9. `auto`: le prove per calcolo

**Scelta.** `auto` riduce l'obiettivo e poi procede così:
- se arriva a `⊤`, la prova è `tt`;
- se è un'uguaglianza, la prova è `refl`;
- su una relazione induttiva cerca una prova componendo costruttori, in profondità limitata;
- su una negazione costruisce e fa verificare l'albero dei pattern assurdi.

Quando fallisce su una congiunzione dice quale parte non vale.

**Perché.** Le politiche di CI sono quasi sempre decidibili su dati concreti, come «nessuna immagine con tag `:latest`» o «subnet disgiunte»: devono costare una parola, non una dimostrazione. `auto` produce un termine, e il kernel lo ricontrolla.

**Costo.** Non c'è ricerca generale: obiettivi con metavariabili e profondità oltre il limite falliscono. È voluto, perché `auto` deve restare prevedibile.

## 10. Numerali nativi

**Scelta.** Nella logica `Nat` è `zero` e `add1`; nel valutatore un numero è un intero. Le definizioni legate alle chiavi `plus`, `monus`, `times`, `leq?`, `lt?`, `nat-eq?` e `pow2` si calcolano nativamente, come in Lean.

**Perché.** Un istante è un numero di secondi nell'ordine dei miliardi, e in unario non si calcolerebbe.

**Costo.** È una scorciatoia fidata. `tests/test.ss` confronta ogni operazione accelerata con le sue clausole unarie, e una mutazione viene presa.

## 11. Il confine tra nucleo e libreria

Tre meccanismi, tutti riservati alla libreria tranne `import`.

**`extern`: solo tipi opachi e primitive pure.** `String`, `contains?`, `concat`, `show`, `re?` (un'espressione regolare su tutta la stringa) e pochi altri: calcolano soltanto sui letterali. Con `re?` una libreria si definisce i suoi tipi raffinati, come `Bucket` e `Arn` in `aws`, senza toccare il nucleo. Un extern non mente, perché restituisce un tipo opaco o calcola, mai una proposizione e mai un dato del mondo. Precedente: Elm 0.19, che ha riservato il codice nativo ai pacchetti ufficiali.

**`builtin`: il nucleo non nomina la libreria.** Il nucleo ha un elenco chiuso di chiavi (`nat`, `zero`, `suc`, `list`, `string`, `abs`, `ip`, `obj`, `host`…). La libreria lega ciascuna a un suo nome con `(builtin chiave nome)`, come i `BUILTIN` di Agda. Passano da qui:
- i letterali `0`, `"x"`, `/out` e `[a b]`;
- le prove di `auto` (`⊤`, `≡`, `⊥`);
- l'accelerazione;
- il piano e l'input di `main`.

Il controllo verifica che il nome esista e sia del genere giusto (tipo, costruttore, definizione), non che abbia la forma attesa. Per questo è fidato quanto `extern`.

**`import`: moduli per nome.** `(import dagger time)` carica `lib/dagger.disegno` e `lib/time.disegno`, una volta sola, in un unico spazio di nomi. Il nome è una parola, non un percorso, così un programma non può far caricare un proprio file con i privilegi della libreria. Il prelude si carica sempre.

| Modulo | Contenuto | Importa |
|---|---|---|
| `prelude` | la teoria: ≡, ⊥, ⊤, Bool, So, Nat, ≤, List, Σ, Either, Every; i builtin logici; nessun extern | sempre caricato |
| `text` | `String` e le primitive pure sulle stringhe | |
| `affine` | `Affine`, i naturali come spazio affine, gli intervalli | |
| `paths` | `Segment`, `Abs`, `Rel`, `⊑`, `⋔` e la legge affine | text, affine |
| `time` | istanti, durate, finestre | affine |
| `net` | `Ip`, `Cidr`, `Port` | text, affine |
| `dagger` | `Image`, `Arg`, `engine` (generato), `Host`, `Export`, i nomi corti, le proprietà del piano | text, paths, net |
| `aws` | la CLI fissata per digest, le credenziali come segreti; `Region`, `Bucket`, `Arn` controllati mentre si tipa; il cloud o LocalStack come service (`Endpoint`); il Parameter Store (`put-parameter`, `put-secure-parameter`, `parameter-exists?`, `parameter-is?`, `Parameters-within`) e S3 (`make-bucket`, `s3-sync`, `s3-put`, `s3-exists?`, `s3-includes?`); `aws-command?` riconosce un comando della CLI per `Before` e `Precedes` | dagger |
| `files` | directory come valori (`file`, `put-file`, `merge`, `only`, `except` per glob), che cosa scrivono (`writes`, `Disjoint-writes`, `Writes-within`), osservazioni sul contenuto guardate da Dagger (`includes?`, `matches?`, `empty?`, `same-content?`) | dagger |

**Perché.** Così il prelude da solo è la teoria dei tipi, e lo si vede: i capitoli 1–4 del libro si controllano senza importare nulla. Il dominio (percorsi, rete, Dagger) diventa una libreria come le altre, e il nucleo non ha nomi di dominio nel codice.

**Costo.** Uno spazio di nomi solo: niente nomi qualificati né import selettivi. Un ciclo tra moduli si ferma in silenzio. In un linguaggio con una libreria chiusa basta così. Le librerie sono curate nel repo, con uno scope che cresce nel tempo, come i pacchetti ufficiali di Elm: non si importano librerie esterne, e una nuova integrazione (cloud, strumenti DevOps) è un nuovo modulo di `lib/`.

## 12. La superficie

**Scelta.** Il linguaggio usa le s-espressioni, ma le quadre sono sintassi:
- in una firma `[x T]` è un binder, `(x T)` un'applicazione;
- in un termine `["a" "b"]` è una lista;
- nelle definizioni le quadre raccolgono pattern o campi.

Inoltre:
- `pipe` passa il valore come primo argomento, come l'oggetto di un metodo GraphQL;
- i campi dello schema si scrivono senza prefisso: `(with-exec c …)` si risolve in `Container.with-exec` perché `c` è un `Container`;
- le parole riservate sono solo `→ Type _ pipe auto let`.

**Perché.** Le s-espressioni non hanno precedenze né ambiguità, e il reader di Chez le legge già. Le quadre rimettono nel testo la distinzione tra legare e applicare che le parentesi da sole cancellano. La risoluzione dei nomi corti guidata dal tipo tiene lo schema fuori dal programma.

**Costo.** Un apice nei nomi (`f'`) è la `quote` del reader, quindi non si usa.

## 13. Errori e strumenti

**Scelta.**
- Gli errori hanno il formato dei compilatori, `file:riga:colonna: messaggio`, e un file riporta tutti i suoi errori. Una dichiarazione sbagliata non ferma le successive, e i «nome sconosciuto» che derivano da una firma fallita si tacciono.
- L'LSP (`disegno lsp`) controlla ogni documento in un processo a sé.

**Perché.** Il formato dei compilatori lo leggono senza adattatori `:make`, la quickfix di Neovim e le annotazioni di GitHub. Il processo separato è la cosa più semplice e corretta, perché il checker tiene stato globale (globali, metavariabili, moduli importati) e ogni controllo deve partire pulito. Un controllo costa circa 0,3 s.

**Costo.**
- Il reader conserva le posizioni delle liste, non dei singoli nomi: l'hover e la definizione funzionano solo sui nomi globali, e un errore su un nome indica la sua lista.
- Il processo separato rifà il controllo della libreria a ogni richiesta.

## 14. L'ospite e la piattaforma

**Scelta.**
- L'ospite è Chez Scheme.
- Il runner è un client della sessione Dagger, HTTP su socket con un parser JSON scritto a mano, non un SDK.
- Dagger è la piattaforma, come la BEAM per Gleam.

**Perché.** L'ecosistema dell'ospite non conta: serve un substrato piccolo per un valutatore nostro. Racket gira su Chez e Idris 2 compila verso Chez, quindi scegliere Chez toglie uno strato. Dang, il linguaggio nativo di Dagger 1.0, conferma che un linguaggio con Dagger come runtime è percorribile. Disegno vi aggiunge la teoria di Martin-Löf, la totalità e un piano ispezionabile.

## La base fidata

| Parte | Dove | Come si verifica |
|---|---|---|
| Kernel e conversione | `src/types.ss`, sezioni kernel e unificazione | test di rifiuto, ricontrollo di ogni termine |
| Pattern, copertura, terminazione, positività | `src/types.ss` | un test di rifiuto per ciascuno |
| Builtin ed extern | `lib/*.disegno`, `prims` e `readers` in `src/types.ss` | accelerazione confrontata con le clausole; letterali in `checks.disegno` |
| Runner | `src/plan.ss` | piani a secco e test dal vivo |
| Generatore | `tools/gen.ss` | `engine.disegno` committato e rivisto |

Tutto il resto, cioè l'elaboratore, la libreria non `extern` e i programmi, lo verifica il kernel.

## Che cosa si cambierebbe per primo

In ordine di valore per costo:
1. **Cumulatività degli universi**: tocca solo il confronto dei livelli.
2. **Il modulo di un nome sconosciuto nel messaggio d'errore**: «Port è in net: (import net)».
3. **Posizioni dei nomi nel reader**: hover e definizione sulle variabili locali.
4. **Definizioni mutue**: oggi non servono alla libreria.
