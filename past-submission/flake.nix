{
  description = "A devShell example";

  inputs = {
    nixpkgs.url      = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url  = "github:numtide/flake-utils";
    # coq-lsp = { type = "git"; url = "https://github.com/ejgallego/coq-lsp.git"; submodules = true; };
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };
      in
      with pkgs;
      {
        devShell = mkShell rec {
          buildInputs = with coqPackages_8_16; [

            texlab
            python312Packages.pygments
           (texlive.combine {
                    inherit (texlive)
                      scheme-small

                      acmart
                      xstring
                      totpages
                      environ
                      hyperxmp
                      ncctools
                      comment
                      ifmtarg

                      cancel
                      cclicenses
                      doublestroke
                      framed
                      relsize
                      yfonts
                      helvetic

                      circledsteps
                      pict2e
                      picture

                      stmaryrd
                      bibtex
                      biblatex
                      enumitem
                      todonotes
                      makebox
                      csquotes
                      libertine
                      lualatex-math
                      scalerel
                      prftree
                      mathpartir
                      tikz-cd
                      pgfplots
                      tensor
                      knowledge
                      currfile
                      cleveref
                      thmtools
                      wrapfig
                      soul
                      multirow
                      threeparttable
                      minted
                      mdframed
                      zref
                      needspace
                      urlbst
                      fontawesome5


                      # build tools
                      latexmk
                      biber
                      ;
                  })           # coq-lsp.packages.${system}.coq-lsp
          ];
        };
      }
      );
  }
