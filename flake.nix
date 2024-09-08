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

  outputs =
    { self
    , nixpkgs
    , gitignore
    , rust-overlay
    }:
    let
      inherit (gitignore.lib) gitignoreSource;

      supportedSystems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      nixpkgsFor = forAllSystems (system:
      import nixpkgs {
          inherit system; 
          overlays = [rust-overlay.overlays.default];
      });

    in
    {

      devShell = forAllSystems (system:
        let
          pkgs = nixpkgsFor."${system}";
        in
        pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.cargo-watch
            pkgs.bacon
            pkgs.rustfmt
            pkgs.cargo

            pkgs.rust-bin.nightly.latest.default
            pkgs.rust-bin.nightly.latest.rust-analyzer
            pkgs.lld
            pkgs.trunk


            pkgs.mermaid-cli
          ];
          RUST_LOG = "info";
          RUST_BACKTRACE = 1;
        });
    };
}


