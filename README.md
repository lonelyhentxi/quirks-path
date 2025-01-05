# quirks-path

A Rust path library with quirks that is as platform-agnostic as possible.

## Install

```shell
cargo install quirks-path
```

## Usage

```
use quirks_path::{ Path, PathBuf };
```

## Support

- *nix Paths (without `/`): `/bin/sh`
- Windows Verbatim: `\\?\cat_pics`
- Windows Verbatim UNC: `\\?\UNC\server\share`
- Windows Verbatim Disk: `\\?\C:`
- Windows DeviceNS: `\\.\COM42`
- Windows UNC: `\\server\share`
- Windows Disk: `C:`

## Quirks

- Think any of / or \ be a seperator or special mark

- Prefer think paths that not have verbatim prefix and start with / be *nix-like root paths

- Prefer think paths start with drive as windows drive paths, and if not contains / sep then default use \ sep

- When call absolute method it will not trim components trailing space and dots (windows style) and not remove parent ..

- Prefer think paths that not have verbatim prefix and start with \\ be *windows-like root paths

- Lack of extra information, think COM1 as relative path
