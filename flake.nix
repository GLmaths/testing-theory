{
  description = "Build an opam project with multiple packages";
  inputs.opam-nix.url = "github:tweag/opam-nix";
  inputs.opam-repository.url = "github:ocaml/opam-repository";
  inputs.opam-repository.flake = false;
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "github:nixos/nixpkgs";
  outputs =
    {
      self,
      nixpkgs,
      opam-nix,
      opam-repository,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (system: {
      legacyPackages =
        let
          opam-rocq = nixpkgs.legacyPackages.${system}.fetchFromGitHub {
            owner = "rocq-prover";
            repo = "opam";
            rev = "7d31d01112bce9dd010f05cbf4c16c0d8f80f486";
            sha256 = "vR2Z8rTqtCPI1xACuod2d4c/4LPyafeMrXWoxqJmR9M=";
            fetchSubmodules = true;
          };
          inherit (opam-nix.lib.${system}) queryToScope;
          scope = queryToScope {
                repos = [
                  "${opam-repository}"
                  "${opam-rocq}/released"
                ];
              }
              {
                # rocq-prover = "*";
                # coq = "*";
                coq-autosubst-ocaml = "*";
                # coq-inf-seq-ext = "*";
                ocaml-base-compiler = "*";
                coq-stdpp = "*";
                coq-lsp = "*";
                # ocaml-lsp = "*";
              };
        in
        scope;
      # packages.default = self.legacyPackages.${system}.rocq;
      packages.default = nixpkgs.legacyPackages.${system}.bash;
      devShells.default = nixpkgs.legacyPackages.${system}.mkShell {
          # buildInputs = with nixpkgs.legacyPackages.${system}; [
          buildInputs = with self.legacyPackages.${system}; [
            coq-autosubst-ocaml
            coq-stdpp
            coq-lsp
            # ocaml
            # opam
          ];
          # shellHook = ''
          #   echo "OCaml development environment"
          #   echo "Available packages: ${builtins.toString (builtins.attrNames self.legacyPackages.${system})}"
          # '';
        };

    });
}

