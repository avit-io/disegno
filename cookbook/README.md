# Cookbook

Ricette brevi, ciascuna un programma a sé e commentato. Si leggono in ordine; tutte sono verificate dai test (tipi, teoremi e piano a secco).

| Ricetta | Mostra | Comando |
|---|---|---|
| [00-basics](00-basics.disegno) | `data`, `def`, pattern, prove per induzione, `record` con invarianti, `auto` | `disegno check` |
| [01-files](01-files.disegno) | `Host` ed `Export`, directory come valori, una configurazione resa come testo | `disegno plan` / `run` |
| [02-go-build](02-go-build.disegno) | container, `pipe`, nomi del motore senza prefisso, percorsi come punti, cache, montaggi disgiunti per ogni sorgente | `disegno plan` / `run` |
| [03-release](03-release.disegno) | `branch` sull'esito dei test, `publish`, il teorema test-prima-di-publish | `disegno plan` |
| [04-literals](04-literals.disegno) | letterali tipati (immagini, percorsi, tempo, IP, porte), spazi affini, gli errori di tipo | `disegno check` |
| [05-network](05-network.disegno) | una rete come dato: subnet disgiunte e nella VPC, porte, finestre, la configurazione generata | `disegno plan` / `run` |
| [06-theorems](06-theorems.disegno) | scrivere una propria politica sul piano, provarla e provarne la violazione, una legge per induzione | `disegno check` |
| [07-file-checks](07-file-checks.disegno) | che cosa scrive una directory, provato per ogni sorgente; `branch` sul contenuto di un file guardato da Dagger | `disegno plan` / `run` |
| [08-release-flow](08-release-flow.disegno) | effetti in sequenza: test, deploy in staging, controllo sul mondo, deploy in prod; i teoremi «test prima del deploy» e «prod dopo staging» | `disegno plan` / `run` |
| [09-aws-parameters](09-aws-parameters.disegno) | AWS Parameter Store: credenziali come segreti (`Host-secret`), parametri scritti dopo il test, tutti sotto `/app/prod`, nessuno due volte | `disegno plan` / `run` |

Con `nix run` al posto di `disegno`: `nix run github:avit-io/disegno -- plan cookbook/02-go-build.disegno`.

I tre comandi sono i tre momenti del disegno: `check` verifica il disegno interno (tipi e teoremi), `plan` stampa il disegno esterno (il piano GraphQL, uno per ogni esito dei `branch`), `run` realizza l'opera su Dagger. I percorsi relativi di `Host` ed `Export` si intendono rispetto alla cartella della ricetta: `run` scrive in `cookbook/bin/`, `cookbook/out/`, `cookbook/net/`.
