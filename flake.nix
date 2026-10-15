{
  description = "Disegno — un linguaggio totale su Dagger";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    dagger.url = "github:dagger/nix";
    dagger.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, dagger, ... }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      d = dagger.packages.${system}.dagger;

      # Motore Dagger dedicato con il bundle CA dell'host (proxy TLS aziendale): il motore
      # installa le CA in /usr/local/share/ca-certificates e le passa ai container che esegue.
      # ponytail: se il bundle dell'host cambia, `docker rm -f disegno-engine` e si ricrea.
      engine = pkgs.writeShellScript "disegno-engine" ''
        if ! docker inspect -f '{{.State.Running}}' disegno-engine 2>/dev/null | grep -q true; then
          docker rm -f disegno-engine >/dev/null 2>&1
          docker run -d --privileged --name disegno-engine \
            -v "$(readlink -f /etc/ssl/certs/ca-bundle.crt)":/usr/local/share/ca-certificates/host-bundle.crt:ro \
            -v disegno-engine:/var/lib/dagger registry.dagger.io/engine:v${d.version} >/dev/null
        fi
      '';

      # disegno [check|plan|run] programma.disegno, disegno lsp: un solo binario.
      # run apre da sé la sessione Dagger.
      disegno = pkgs.writeShellScriptBin "disegno" ''
        main=${self}/src/main.ss
        export DISEGNO_SCHEME=${pkgs.chez}/bin/scheme      # per i controlli che lancia disegno lsp
        if [ "$1" = run ]; then
          if [ -z "$_EXPERIMENTAL_DAGGER_RUNNER_HOST" ]; then
            ${engine}
            export _EXPERIMENTAL_DAGGER_RUNNER_HOST=docker-container://disegno-engine
          fi
          export DAGGER_NO_NAG=1
          progress=""                                     # in CI, o senza terminale: niente TUI, log per passo
          if [ -n "$CI" ] || [ ! -t 1 ]; then export DISEGNO_LOGS=1; progress=--silent; fi
          exec ${d}/bin/dagger run $progress ${pkgs.chez}/bin/scheme --script "$main" "$@"
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
    in {
      packages.${system} = { default = disegno; inherit grammar nvim-disegno; };
      apps.${system}.default = { type = "app"; program = "${disegno}/bin/disegno"; };

      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.chez d disegno ];
        shellHook = ''
          ${engine}
          export _EXPERIMENTAL_DAGGER_RUNNER_HOST=docker-container://disegno-engine DAGGER_NO_NAG=1
        '';
      };
    };
}
