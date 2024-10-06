{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";

    gitignore = {
      url = "github:hercules-ci/gitignore.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    nixpkgs,
    gitignore,
    rust-overlay,
  }: let
    inherit (gitignore.lib) gitignoreSource;

    supportedSystems = ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"];
    forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
    nixpkgsFor = forAllSystems (system:
      import nixpkgs {
        inherit system;
        overlays = [rust-overlay.overlays.default self.overlays.default];
      });
  in {
    overlays.default = final: prev: {
      tbsp = with final; let
        pname = "tbsp";
        packageMeta = (lib.importTOML ./Cargo.toml).package;
        rustPlatform = makeRustPlatform {
          inherit (final) cargo rustc;
        };
      in
        rustPlatform.buildRustPackage {
          inherit pname;
          inherit (packageMeta) version;

          src = self;
          cargoLock.lockFile = ./Cargo.lock;

          meta = with lib; {
            description = "tree-based source processing language";
            homepage = "https://git.peppe.rs/languages/tbsp/about";
            license = licenses.mit;
          };
        };
    };

    defaultPackage = forAllSystems (system: nixpkgsFor."${system}".tbsp);
    formatter = forAllSystems (system: nixpkgsFor."${system}".alejandra);

    devShell = forAllSystems (system: let
      pkgs = nixpkgsFor."${system}";
    in
      pkgs.mkShell {
        nativeBuildInputs = [
          pkgs.cargo-watch
          pkgs.bacon
          pkgs.rustfmt
          pkgs.cargo

          pkgs.rust-bin.nightly.latest.default
          pkgs.rust-analyzer

          pkgs.mermaid-cli
        ];
        RUST_LOG = "info";
        RUST_BACKTRACE = 1;
      });
  };
}
