#!/usr/bin/env bash
# Install Zig 0.15.2 onto PATH for the CI job.
#
# The tarball is the one ziglang.org publishes for this version. The sha256
# is the digest in https://ziglang.org/download/index.json.
set -euo pipefail

version=0.15.2

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) target=aarch64-macos ;;
  Darwin-x86_64) target=x86_64-macos ;;
  Linux-x86_64) target=x86_64-linux ;;
  Linux-aarch64 | Linux-arm64) target=aarch64-linux ;;
  *)
    echo "no Zig ${version} build for $(uname -s) $(uname -m)" >&2
    exit 1
    ;;
esac

case "$target" in
  aarch64-macos) sum=3cc2bab367e185cdfb27501c4b30b1b0653c28d9f73df8dc91488e66ece5fa6b ;;
  x86_64-macos) sum=375b6909fc1495d16fc2c7db9538f707456bfc3373b14ee83fdd3e22b3d43f7f ;;
  x86_64-linux) sum=02aa270f183da276e5b5920b1dac44a63f1a49e55050ebde3aecc9eb82f93239 ;;
  aarch64-linux) sum=958ed7d1e00d0ea76590d27666efbf7a932281b3d4044a8b707e1784c8074a61 ;;
esac

file="zig-${target}-${version}.tar.xz"
url="https://ziglang.org/download/${version}/${file}"
root="${RUNNER_TEMP:-/tmp}/zig-${version}"
mkdir -p "$root"
tmp="${root}.tar.xz"

ok=0
for _ in 1 2 3 4 5; do
  if curl -fsSL --connect-timeout 20 --max-time 180 -o "$tmp" "$url"; then
    ok=1
    break
  fi
  sleep 3
done

if [ "$ok" != 1 ]; then
  echo "could not download ${url}" >&2
  exit 1
fi

echo "${sum}  ${tmp}" | shasum -a 256 -c -
rm -rf "$root"
mkdir -p "$root"
tar -xJf "$tmp" -C "$root" --strip-components=1
rm -f "$tmp"

if [ -n "${GITHUB_PATH:-}" ]; then
  echo "$root" >>"$GITHUB_PATH"
fi

"$root/zig" version
