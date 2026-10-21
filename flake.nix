{
  description = "Disegno — a total language on Dagger";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
  };

  outputs = { self, nixpkgs, ... }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};

      # Dagger 1.0, still in beta: github:dagger/nix has only the stable versions.
      # ponytail: x86_64-linux only; back to dagger/nix when 1.0 is out.
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

      # The Dagger engine. Normally Dagger decides: if there is none, the CLI starts one on the
      # host's Docker, with the version in its name (dagger-engine-v…), and versions coexist.
      # Disegno starts its own only to mount a CA bundle into it (corporate TLS proxy): the engine
      # installs the CAs in /usr/local/share/ca-certificates and passes them to the containers it runs.
      # DISEGNO_HOST_CA picks the bundle: a host path, or none; without it, the system's if there is
      # one (/etc/ssl/certs/ca-bundle.crt: NixOS yes, Ubuntu no). In Disegno's container it is
      # none, because its paths are not those of the host on which Docker mounts the volumes.
      # The script prints the engine's name, or nothing if Dagger's will do.
      # ponytail: if the host's bundle changes, `docker rm -f disegno-engine-v…` and it is recreated.
      engine = pkgs.writeShellScript "disegno-engine" ''
        host_ca="''${DISEGNO_HOST_CA:-}"
        if [ -z "$host_ca" ] && [ -e /etc/ssl/certs/ca-bundle.crt ]; then
          host_ca=$(readlink -f /etc/ssl/certs/ca-bundle.crt)
        fi
        [ -n "$host_ca" ] && [ "$host_ca" != none ] || exit 0
        name=disegno-engine-v${d.version}
        if [ "$(docker inspect -f '{{.State.Running}}' $name 2>/dev/null)" != true ]; then
          docker rm -f $name >/dev/null 2>&1
          docker run -d --privileged --name $name \
            -v "$host_ca:/usr/local/share/ca-certificates/host-bundle.crt:ro" \
            -v $name:/var/lib/dagger registry.dagger.io/engine:v${d.version} >/dev/null
        fi
        echo $name
      '';

      # disegno [check|plan|run] program.disegno, disegno lsp: a single binary.
      # run opens the Dagger session itself.
      disegno = pkgs.writeShellScriptBin "disegno" ''
        main=${self}/src/main.ss
        export DISEGNO_SCHEME=${pkgs.chez}/bin/scheme      # for the checks disegno lsp launches
        if [ "$1" = run ]; then
          if [ -z "$DAGGER_ENGINE" ]; then
            name=$(${engine})
            if [ -n "$name" ]; then export DAGGER_ENGINE=container://$name; fi
          fi
          export DAGGER_NO_NAG=1
          progress=""                                     # in CI, or without a terminal: no TUI, per-step logs
          if [ -n "$CI" ] || [ ! -t 1 ]; then export DISEGNO_LOGS=1; progress=--silent; fi
          exec ${d}/bin/dagger api with-session $progress ${pkgs.chez}/bin/scheme --script "$main" "$@"
        fi
        exec ${pkgs.chez}/bin/scheme --script "$main" "$@"
      '';

      # The tree-sitter parser, generated from editors/tree-sitter-disegno/grammar.js.
      grammar = pkgs.tree-sitter.buildGrammar {
        language = "disegno";
        version = "0.1.0";
        src = ./editors/tree-sitter-disegno;
        generate = true;
      };

      # Neovim plugin: filetype, tree-sitter highlighting, :make with the quickfix.
      nvim-disegno = pkgs.runCommand "nvim-disegno" { } ''
        mkdir -p $out/parser $out/queries/disegno $out/ftdetect $out/ftplugin
        cp ${grammar}/parser $out/parser/disegno.so
        cp ${./editors/tree-sitter-disegno/queries}/*.scm $out/queries/disegno/
        cp ${./editors/nvim/ftdetect/disegno.lua} $out/ftdetect/disegno.lua
        substitute ${./editors/nvim/ftplugin/disegno.lua} $out/ftplugin/disegno.lua \
          --replace-fail @disegno@ ${disegno}/bin/disegno
      '';
      # Disegno as an image, for a CI without Nix (Jenkins, GitLab):
      #   docker run --rm --user "$(id -u):$(id -g)" --group-add "$(stat -c %g /var/run/docker.sock)" \
      #     -v /var/run/docker.sock:/var/run/docker.sock -v "$PWD:/work" -w /work \
      #     -e ENVIRONMENT -e TAG … ghcr.io/avit-io/disegno:<commit> run .ci/release.disegno
      # The Dagger engine runs as a container alongside, on the host's Docker (socket mounted); with
      # --user the exported files belong to whoever runs it, not to root.
      image = pkgs.dockerTools.buildLayeredImage {
        name = "ghcr.io/avit-io/disegno";
        tag = "latest";
        contents = [ disegno (pkgs.docker_29.override { clientOnly = true; }) pkgs.coreutils pkgs.bash ];   # client only: the daemon is the host's
        extraCommands = "mkdir -m 1777 tmp work";
        config = {
          Entrypoint = [ "${disegno}/bin/disegno" ];
          WorkingDir = "/work";
          Env = [ "PATH=/bin" "HOME=/tmp" "DISEGNO_HOST_CA=none" ];
          Labels."org.opencontainers.image.source" = "https://github.com/avit-io/disegno";
          Labels."org.opencontainers.image.description" = "Disegno: a total language with dependent types for CI/CD, on Dagger";
        };
      };
    in {
      packages.${system} = { default = disegno; inherit grammar nvim-disegno image; };
      apps.${system}.default = { type = "app"; program = "${disegno}/bin/disegno"; };

      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.chez d disegno ];
        shellHook = ''
          name=$(${engine})                                 # an engine with the CAs, or Dagger's
          if [ -n "$name" ]; then export DAGGER_ENGINE=container://$name; fi
          export DAGGER_NO_NAG=1
          export DISEGNO_TEST_KEY=test                      # fake key for LocalStack, in the live tests
        '';
      };
    };
}
