{
  description = "Disegno — un linguaggio totale su Dagger";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    dagger.url = "github:dagger/nix";
    dagger.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { nixpkgs, dagger, ... }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells.${system}.default = let d = dagger.packages.${system}.dagger; in pkgs.mkShell {
        packages = [ pkgs.chez d ];
        # Motore Dagger dedicato con il bundle CA dell'host (proxy TLS aziendale): il motore
        # installa le CA in /usr/local/share/ca-certificates e le passa ai container che esegue.
        # ponytail: se il bundle dell'host cambia, `docker rm -f disegno-engine` e si ricrea.
        shellHook = ''
          export _EXPERIMENTAL_DAGGER_RUNNER_HOST=docker-container://disegno-engine DAGGER_NO_NAG=1
          if ! docker inspect -f '{{.State.Running}}' disegno-engine 2>/dev/null | grep -q true; then
            docker rm -f disegno-engine >/dev/null 2>&1
            docker run -d --privileged --name disegno-engine \
              -v "$(readlink -f /etc/ssl/certs/ca-bundle.crt)":/usr/local/share/ca-certificates/host-bundle.crt:ro \
              -v disegno-engine:/var/lib/dagger registry.dagger.io/engine:v${d.version} >/dev/null
          fi
        '';
      };
    };
}
