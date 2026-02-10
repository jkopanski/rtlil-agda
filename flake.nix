{
  description = "Yosys RTL Intermediate Language for Agda";

  inputs = {
    overture.url = "sourcehut:~madnat/overture";
    nixpkgs.follows = "overture/nixpkgs";
    utils.follows = "overture/utils";
    cheshire = {
      url = "github:jkopanski/cheshire";
      inputs.overture.follows = "overture";
    };
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
            inputs.overture.overlays.default
            self.overlays.default
          ];
        };
        agdaWithLibraries = pkgs.agda.withPackages {
          pkgs = (p: [
            p.standard-library
            p.prettyprint
            inputs.overture.outputs.packages.${system}.default
            inputs.cheshire.outputs.packages.${system}.default
          ]);

          ghc = pkgs.haskellPackages.ghcWithPackages (p: with p; [ clock ieee754 ]);
        };

      in {
        checks.whitespace = pkgs.stdenvNoCC.mkDerivation {
          name = "check-whitespace";
          dontBuild = true;
          src = ./.;
          doCheck = true;
          checkPhase = ''
            ${pkgs.haskellPackages.fix-whitespace.bin}/bin/fix-whitespace --check
          '';
          installPhase = ''mkdir "$out"'';
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithLibraries
            pkgs.haskellPackages.fix-whitespace
            pkgs.yosys
            pkgs.xdot
            self.outputs.packages.${system}.convert2il
          ];
        };

        packages = {
          rtlil-agda = pkgs.agdaPackages.mkDerivation {
            pname = "rtlil-agda";
            version = "0.0.1";
            src = ./rtlil-agda;

            buildInputs = with pkgs.agdaPackages; [
              standard-library
              prettyprint
              inputs.overture.outputs.packages.${system}.default
              inputs.cheshire.outputs.packages.${system}.default
            ];

            meta = {
              description = "Yosys RTL Intermediate Language for Agda";
              homepage = "https://git.sr.ht/~madnat/rtlil";
            };
          };

          rtlil-cheshire = pkgs.agdaPackages.mkDerivation {
            pname = "rtlil-cheshire";
            version = "0.0.1";
            src = ./rtlil-cheshire;

            buildInputs = with pkgs.agdaPackages; [
              standard-library
              prettyprint
              inputs.overture.outputs.packages.${system}.default
              inputs.cheshire.outputs.packages.${system}.default
              self.outputs.packages.${system}.rtlil-agda
            ];

            meta = {
              description = "Yosys RTL Intermediate Language for Agda";
              homepage = "https://git.sr.ht/~madnat/rtlil";
            };
          };

          convert2il = pkgs.runCommand "convert2il" {
            buildInputs = [ pkgs.fish ];
            nativeBuildInputs = [ pkgs.makeWrapper ];
            meta.mainPropgram = "convert2il";
            src = ./.;
          } ''
            mkdir -p $out/bin
            install -m +x ${./scripts/convert2il.fish} $out/bin/convert2il
            patchShebangs $out/bin/convert2il

            wrapProgram $out/bin/convert2il \
              --prefix PATH : ${pkgs.lib.makeBinPath [ pkgs.yosys ]}
          '';
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
