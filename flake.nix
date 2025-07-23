{
  description = "Yosys RTL Intermediate Language for Agda";

  inputs = {
    cheshire.url = "github:jkopanski/cheshire";
    nixpkgs.follows = "cheshire/nixpkgs";
    utils.follows = "cheshire/utils";
    prettyprint = {
      url = "github:agda/agda-pretty/v1.0";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, utils, ... }:
    (utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            inputs.cheshire.outputs.overlays.default
            self.overlays.default
          ];
        };
        agdaWithLibraries = pkgs.agda.withPackages (p: [
          p.standard-library
          p.prettyprint
          inputs.cheshire.outputs.packages.${system}.default
        ]);

      in {
        checks.whitespace = pkgs.stdenvNoCC.mkDerivation {
          name = "check-whitespace";
          dontBuild = true;
          src = ./.;
          doCheck = true;
          checkPhase = ''
            ${pkgs.haskellPackages.fix-whitespace}/bin/fix-whitespace --check
          '';
          installPhase = ''mkdir "$out"'';
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithLibraries
            pkgs.haskellPackages.fix-whitespace
          ];
        };

        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "rtlil";
          version = "0.0.1";
          src = ./.;

          everythingFile = "./src/Everything.agda";

          buildInputs = with pkgs.agdaPackages; [
            standard-library
            inputs.cheshire.outputs.packages.${system}.default
          ];

          meta = {
            description = "Yosys RTL Intermediate Language for Agda";
            homepage = "https://git.sr.ht/~madnat/rtlil";
          };
        };
      }
    )) // {
      overlays.default = final: prev: {
        agdaPackages = prev.agdaPackages.overrideScope (
          finalAgda: prevAgda: {
            prettyprint = final.agdaPackages.mkDerivation {
              pname = "prettyprint";
                version = "1.0";
                src = inputs.prettyprint;

                everythingFile = "./src/Text/PrettyPrint.agda";
                libraryFile = "prettyprint.agda-lib";

                buildInputs = with final.agdaPackages; [
                  standard-library
                ];

                meta = with final.lib; {
                  description = "More or less complete Agda port of the pretty Haskell package.";
                  homepage = "https://github.com/agda/agda-pretty";
                  license = licenses.bsd3;
                };
            };
          }
        );
      };
    };
}
