{
  description = "Rust and Lean environment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/aff8a0b28396750446e5537a96461bc4facdb287";

  outputs = { nixpkgs, ... }:
    let
      system = "aarch64-darwin";
      pkgs = import nixpkgs { inherit system; };

      toolchain = (builtins.fromTOML (builtins.readFile ./rust/rust-toolchain.toml)).toolchain.channel;

      extractionRoots = [
        "phd_core::arithmetic::modulo"
      ];
      extractionArgs = pkgs.lib.escapeShellArgs (
        pkgs.lib.concatMap (root: [ "--start-from" root ]) extractionRoots
      );

      hax = pkgs.stdenvNoCC.mkDerivation {
        pname = "cargo-hax";
        version = "0.4.0";

        src = pkgs.fetchurl {
          url = "https://github.com/cryspen/hax/releases/download/cargo-hax-v0.4.0/cargo-hax-aarch64-apple-darwin.tar.zst";
          sha256 = "e64a4feaae3a551f5b241bcad08e405cfe154224a5372065961c79e2abfa523b";
        };

        nativeBuildInputs = [ pkgs.zstd ];

        unpackPhase = ''tar --zstd -xf "$src"'';
        installPhase = ''install -Dm755 cargo-hax "$out/bin/cargo-hax"'';
      };

      extract = pkgs.writeShellApplication {
        name = "hax-lean";
        runtimeInputs = [ pkgs.rustup pkgs.coreutils ];

        text = ''
          cache_root="''${XDG_CACHE_HOME:-$HOME/.cache}/hax/sysroots"
          export MIRI_SYSROOT="$cache_root/${toolchain}-${system}"
          unset HAX_AENEAS_BINARY HAX_CHARON_BINARY RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER
          rustup run ${toolchain} cargo miri setup
          extraction_args=${pkgs.lib.escapeShellArg extractionArgs}
          exec ${hax}/bin/cargo-hax hax into lean \
            --charon-args="--sysroot '$MIRI_SYSROOT' $extraction_args" "$@"
        '';
      };
    in {
      devShells.${system}.default = pkgs.mkShell {
        packages = [ extract hax pkgs.rustup pkgs.elan pkgs.just pkgs.git ];

        shellHook = ''
          unset HAX_AENEAS_BINARY HAX_CHARON_BINARY RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER
          export RUSTUP_TOOLCHAIN=${toolchain}
          rustup toolchain install ${toolchain} --profile minimal --component rust-src,miri,rustfmt,clippy
        '';
      };
    };
}
