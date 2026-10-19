{
  description = "Disegno — un linguaggio totale su Dagger";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
  };

  outputs = { self, nixpkgs, ... }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};

      # Dagger 1.0, ancora in beta: github:dagger/nix ha solo le versioni stabili.
      # ponytail: solo x86_64-linux; si torna a dagger/nix quando esce la 1.0.
      d = pkgs.stdenvNoCC.mkDerivation rec {
        pname = "dagger";
        version = "1.0.0-beta.18";
        src = pkgs.fetchurl {
          url = "https://dl.dagger.io/dagger/releases/${version}/dagger_v${version}_linux_amd64.tar.gz";
          hash = "sha256-Uyb0iCW2QAhwUpDLKoEJwo5KiNNB73Zb6CNIYKzzL9s=";
        };
        sourceRoot = ".";
        installPhase = "install -Dm755 dagger $out/bin/dagger";
      };

      # Motore Dagger dedicato con il bundle CA dell'host (proxy TLS aziendale): il motore
      # installa le CA in /usr/local/share/ca-certificates e le passa ai container che esegue.
      # Senza bundle (per esempio su Ubuntu, in CI) il motore usa le sue CA.
      # Si ricrea se è fermo o di un'altra versione. DISEGNO_HOST_CA sceglie il bundle: un percorso
      # dell'host, o none; nel container di Disegno vale none, perché i suoi percorsi non sono
      # quelli dell'host su cui Docker monta i volumi.
      # ponytail: se il bundle dell'host cambia, `docker rm -f disegno-engine` e si ricrea.
      engine = pkgs.writeShellScript "disegno-engine" ''
        if [ "$(docker inspect -f '{{.State.Running}} {{.Config.Image}}' disegno-engine 2>/dev/null)" != "true registry.dagger.io/engine:v${d.version}" ]; then
          docker rm -f disegno-engine >/dev/null 2>&1
          ca="" host_ca="''${DISEGNO_HOST_CA:-}"
          if [ -z "$host_ca" ] && [ -e /etc/ssl/certs/ca-bundle.crt ]; then
            host_ca=$(readlink -f /etc/ssl/certs/ca-bundle.crt)
          fi
          if [ -n "$host_ca" ] && [ "$host_ca" != none ]; then
            ca="-v $host_ca:/usr/local/share/ca-certificates/host-bundle.crt:ro"
          fi
          docker run -d --privileged --name disegno-engine $ca \
            -v disegno-engine:/var/lib/dagger registry.dagger.io/engine:v${d.version} >/dev/null
        fi
      '';

      # disegno [check|plan|run] programma.disegno, disegno lsp: un solo binario.
      # run apre da sé la sessione Dagger.
      disegno = pkgs.writeShellScriptBin "disegno" ''
        main=${self}/src/main.ss
        export DISEGNO_SCHEME=${pkgs.chez}/bin/scheme      # per i controlli che lancia disegno lsp
        if [ "$1" = run ]; then
          if [ -z "$DAGGER_ENGINE" ]; then
            ${engine}
            export DAGGER_ENGINE=container://disegno-engine
          fi
          export DAGGER_NO_NAG=1
          progress=""                                     # in CI, o senza terminale: niente TUI, log per passo
          if [ -n "$CI" ] || [ ! -t 1 ]; then export DISEGNO_LOGS=1; progress=--silent; fi
          exec ${d}/bin/dagger api with-session $progress ${pkgs.chez}/bin/scheme --script "$main" "$@"
        fi
        exec ${pkgs.chez}/bin/scheme --script "$main" "$@"
      '';

      # Il parser tree-sitter, generato da editors/tree-sitter-disegno/grammar.js.
      grammar = pkgs.tree-sitter.buildGrammar {
        language = "disegno";
        version = "0.1.0";
        src = ./editors/tree-sitter-disegno;
        generate = true;
      };

      # Plugin per Neovim: filetype, evidenziazione tree-sitter, :make con la quickfix.
      nvim-disegno = pkgs.runCommand "nvim-disegno" { } ''
        mkdir -p $out/parser $out/queries/disegno $out/ftdetect $out/ftplugin
        cp ${grammar}/parser $out/parser/disegno.so
        cp ${./editors/tree-sitter-disegno/queries}/*.scm $out/queries/disegno/
        cp ${./editors/nvim/ftdetect/disegno.lua} $out/ftdetect/disegno.lua
        substitute ${./editors/nvim/ftplugin/disegno.lua} $out/ftplugin/disegno.lua \
          --replace-fail @disegno@ ${disegno}/bin/disegno
      '';
      # Disegno come immagine, per una CI senza Nix (Jenkins, GitLab):
      #   docker run --rm --user "$(id -u):$(id -g)" --group-add "$(stat -c %g /var/run/docker.sock)" \
      #     -v /var/run/docker.sock:/var/run/docker.sock -v "$PWD:/work" -w /work \
      #     -e ENVIRONMENT -e TAG … ghcr.io/avit-io/disegno:<commit> run .ci/release.disegno
      # Il motore Dagger gira come container accanto, sul Docker dell'host (socket montato); con
      # --user i file esportati sono di chi lancia, non di root.
      image = pkgs.dockerTools.buildLayeredImage {
        name = "ghcr.io/avit-io/disegno";
        tag = "latest";
        contents = [ disegno (pkgs.docker_29.override { clientOnly = true; }) pkgs.coreutils pkgs.bash ];   # solo il client: il demone è quello dell'host
        extraCommands = "mkdir -m 1777 tmp work";
        config = {
          Entrypoint = [ "${disegno}/bin/disegno" ];
          WorkingDir = "/work";
          Env = [ "PATH=/bin" "HOME=/tmp" "DISEGNO_HOST_CA=none" ];
          Labels."org.opencontainers.image.source" = "https://github.com/avit-io/disegno";
          Labels."org.opencontainers.image.description" = "Disegno: un linguaggio totale con tipi dipendenti per CI/CD, su Dagger";
        };
      };
    in {
      packages.${system} = { default = disegno; inherit grammar nvim-disegno image; };
      apps.${system}.default = { type = "app"; program = "${disegno}/bin/disegno"; };

      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.chez d disegno ];
        shellHook = ''
          ${engine}
          export DAGGER_ENGINE=container://disegno-engine DAGGER_NO_NAG=1
          export DISEGNO_TEST_KEY=test                      # chiave finta per LocalStack, nei test dal vivo
        '';
      };
    };
}
