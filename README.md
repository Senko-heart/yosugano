# yosugano

Cotopha script executable decompiler (.csx), aiming to restore source code in a way that compiles to a functionally identical binary.

**Important:** this is not a general-purpose decompiler. The primary target is the original, v1.0, physical release of Yosuga no Sora.
You should not expect nor blindly rely on produced results, and in many cases it may crash due to broken assumptions about the code structure.
It's more likely that the older games may decompile correctly.

## Usage

`yosugano [csx-path]` — locates `.csx` file, on success saves the script files: *definitions.ch, variables.cos, file-N.cos...* This may change in the future.

See the official documentation on how to use `cotoco.exe` and `cotolink.exe`. `.cos` files should be compiled and linked in the suggested order above.

## Compiling

Install Rust nightly via [rustup](https://rustup.rs/) or your preferred package manager. Run `cargo build --profile release-pub` in the project folder.

## License

The code in this repository is dual-licensed under either:

- GNU General Public License, Version 2.0 ([LICENSE.GPL2](LICENSE.GPL2))
- GNU General Public License, Version 3.0 ([LICENSE.GPL3](LICENSE.GPL3))

at your option.

### Your contributions

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you shall be dual licensed as above, without any additional terms or conditions.
