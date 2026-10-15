{
  description = "Disegno — un linguaggio totale su Dagger";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
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

      # disegno [check|plan|run] programma.disegno; run apre da sé la sessione Dagger.
      disegno = pkgs.writeShellScriptBin "disegno" ''
        main=${self}/src/main.ss
        if [ "$1" = run ]; then
          if [ -z "$_EXPERIMENTAL_DAGGER_RUNNER_HOST" ]; then
            ${engine}
            export _EXPERIMENTAL_DAGGER_RUNNER_HOST=docker-container://disegno-engine
          fi
          export DAGGER_NO_NAG=1
          exec ${d}/bin/dagger run ${pkgs.chez}/bin/scheme --script "$main" "$@"
        fi
        exec ${pkgs.chez}/bin/scheme --script "$main" "$@"
      '';
    in {
      packages.${system}.default = disegno;
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
