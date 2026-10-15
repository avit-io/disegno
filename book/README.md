# Pointless Disegno

Un libricino per imparare a programmare con i tipi dipendenti, in Disegno. Non serve sapere di logica né di teoria dei tipi: serve leggere con calma, scrivere gli esempi e farli verificare.

## Il filo

Il libro segue un'idea che viene da Gentzen e che Dummett e Prawitz hanno trasformato in una teoria del significato: **il significato di un tipo sta nelle sue regole di introduzione**, cioè nei modi canonici di costruirne un elemento. Le regole di eliminazione, cioè i modi di usarlo, non aggiungono significato: sono giustificate dalle introduzioni, e devono essere in *armonia* con esse, non chiedere più di quanto le introduzioni danno.

In Disegno questa idea è letterale:

- i **costruttori** di un `data` sono le regole di introduzione;
- il **pattern matching** è l'eliminazione, e il controllo di **copertura** verifica l'armonia: ogni introduzione ha il suo caso;
- il **calcolo** è l'eliminazione delle *deviazioni* di Prawitz: un'introduzione subito seguita da un'eliminazione si riduce;
- la **totalità** garantisce che ogni termine chiuso si riduca a una forma canonica, ed è per questo che i teoremi valgono qualcosa.

Programmi e prove si scrivono allo stesso modo. Il libro comincia dai programmi e arriva alle prove senza cambiare strumento.

## Come si legge

Ogni capitolo è un file `.disegno`: il testo sta nei commenti, il codice è codice vero. Leggilo in un editor con il plugin di Disegno (l'hover mostra i tipi), e verificalo:

```
disegno check book/01-introductions.disegno
```

Se il capitolo passa, tutto ciò che vi è scritto è vero: tipi e teoremi compresi. Gli esercizi stanno in fondo ai capitoli, commentati: togli il `;`, completali, e verifica di nuovo. Le soluzioni, commentate e verificate come i capitoli, sono in [solutions/](solutions/): una per capitolo, con lo stesso nome.

## Indice

| Capitolo | Idea |
|---|---|
| [1. Il significato è nelle introduzioni](01-introductions.disegno) | `data`, forme canoniche, il giudizio `e : T`, il tipo vuoto |
| [2. Eliminare con armonia](02-eliminations.disegno) | pattern matching, inversione, copertura, deviazioni che si riducono |
| [3. Funzioni](03-functions.disegno) | `λ` e applicazione, `the`, argomenti impliciti, polimorfismo |
| [4. Ricorsione e totalità](04-recursion.disegno) | ricorsione strutturale, `ind-Nat` come regola di eliminazione, `rec-Nat`, perché niente ricorsione generale, positività |
| [5. Tipi che dipendono da valori](05-dependent-types.disegno) | famiglie indicizzate (`Vec`), `testa` totale, Π dipendente, il calcolo dentro i tipi |
| [6. L'uguaglianza](06-equality.disegno) | `≡` e `refl`, uguaglianza per calcolo e per prova, `transport` come eliminazione, `+-comm`, `accoda` con `(+ m n)`, assioma K |
| [7. Esiste](07-exists.disegno) | Σ: il testimone e la prova, `fst` e `snd`, per ogni ed esiste, `differenza` come algoritmo, `×` come caso particolare |
| [8. Oppure, e il nulla](08-or-and-nothing.disegno) | `Either` e il ragionamento per casi, pari o dispari, `⊥` e `¬`, il pattern assurdo, De Morgan, il terzo escluso e la sua doppia negazione |
| [9. Le prove come programmi](09-proofs-as-programs.disegno) | Curry–Howard, relazioni induttive (`≤`), decidibilità, `So` e i bit che dicono il vero, che cosa fa `auto`, e uno sguardo al piano |

## Letture

- G. Gentzen, *Untersuchungen über das logische Schließen*, 1935: le introduzioni come definizioni dei segni.
- D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*, 1965: il principio di inversione e la riduzione delle deviazioni.
- M. Dummett, *The Logical Basis of Metaphysics*, 1991: l'armonia e una teoria del significato basata sulle regole.
- W. A. Howard, *The formulae-as-types notion of construction*, 1980 (circolato dal 1969): le proposizioni come tipi.
- P. Martin-Löf, *On the meanings of the logical constants and the justifications of the logical laws*, 1983 (pubblicato nel 1996): il ponte tra queste idee e la teoria dei tipi.
- D. P. Friedman e D. Thrane Christiansen, *The Little Typer*, 2018: lo stesso viaggio, in Pie.
