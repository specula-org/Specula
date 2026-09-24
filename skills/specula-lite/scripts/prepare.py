#!/usr/bin/env python3
"""Prepare Specula Lite's local resources and user-local TLA+ runtime."""

from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
import zipfile
from pathlib import Path, PurePosixPath

SKILL = Path(__file__).resolve().parents[1]
JAVA_RELEASE = "21.0.12.1_1"
JAVA_BASE = "https://github.com/adoptium/temurin21-binaries/releases/download/jdk-21.0.12.1%2B1"
JAVA_HASHES = {
    ("linux", "x64"): "2413149700df0f7d440500a84a8f764c535f21e5a5e87d38328b64eec2c5b500",
    ("linux", "aarch64"): "14be1f35ebdbd1f6e8d57eb911a3ffb74d6d9aa255abc5daf2b1302002cf2cf2",
    ("mac", "x64"): "6717ec641fd9ce0bb209ca083ee23b42202ac68cb6fcc5753496e0e4a0f41989",
    ("mac", "aarch64"): "dec50fc6f9fcd4fe3ae8cabf5a5fa68f6afc48841f7698e468e9aa5d54beed84",
    ("windows", "x64"): "d35f31e712f0fcf6ac5a093edc90204fbff22f720ba3950bd09d331d5e621636",
    ("windows", "aarch64"): "e82cc17e0bf89a25b0b0ed106d072f2ea420587d0a6870534b71b1dce3ae28c3",
}
JARS = (
    (
        "tla2tools-1.8.0.jar",
        "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar",
        "32d64fbbc464559fc7192341b27b885fa4eb6b92d1648d2b49fb9cdcb7aacf81",
    ),
    (
        "CommunityModules-202505152026.jar",
        "https://github.com/tlaplus/CommunityModules/releases/download/202505152026/CommunityModules-deps.jar",
        "044e8ecdfbca92d51d7eb4469422c2a7da1fe25dc8ad39c4a90e6622d6da4d99",
    ),
)


def cache_dir() -> Path:
    override = os.environ.get("SPECULA_LITE_CACHE")
    if override:
        return Path(override).expanduser().resolve()
    base = Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache")))
    return (base / "specula-lite").expanduser().resolve()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def download(url: str, destination: Path, expected_hash: str) -> Path:
    if destination.is_file() and sha256(destination) == expected_hash:
        return destination
    destination.parent.mkdir(parents=True, exist_ok=True)
    print(f"Preparing {destination.name}...", file=sys.stderr, flush=True)
    request = urllib.request.Request(url, headers={"User-Agent": "Specula-Lite"})
    with tempfile.NamedTemporaryFile(dir=destination.parent, delete=False) as stream:
        temporary = Path(stream.name)
        try:
            with urllib.request.urlopen(request, timeout=60) as response:
                shutil.copyfileobj(response, stream)
        except BaseException:
            stream.close()
            temporary.unlink(missing_ok=True)
            raise
    try:
        if sha256(temporary) != expected_hash:
            raise RuntimeError(f"Checksum mismatch for {destination.name}; download was not installed")
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)
    return destination


def archive_path(root: Path, name: str) -> Path:
    relative = PurePosixPath(name)
    if relative.is_absolute() or ".." in relative.parts or "\\" in name or ":" in name:
        raise ValueError(f"Unsafe archive path: {name}")
    target = root.joinpath(*relative.parts)
    if not target.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Archive path escapes destination: {name}")
    return target


def extract_archive(archive: Path, destination: Path) -> None:
    """Extract regular files and safe JRE links, including on Python 3.10."""
    if zipfile.is_zipfile(archive):
        with zipfile.ZipFile(archive) as bundle:
            for member in bundle.infolist():
                target = archive_path(destination, member.filename)
                if member.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with bundle.open(member) as source, target.open("xb") as output:
                        shutil.copyfileobj(source, output)
        return
    with tarfile.open(archive) as bundle:
        links = []
        for member in bundle:
            target = archive_path(destination, member.name)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                source = bundle.extractfile(member)
                if source is None:
                    raise ValueError(f"Missing archive content: {member.name}")
                with source, target.open("xb") as output:
                    shutil.copyfileobj(source, output)
                target.chmod(member.mode & 0o777)
            elif member.issym():
                links.append((target, member.linkname))
            else:
                raise ValueError(f"Unsupported archive member: {member.name}")
        # Defer links so file writes never traverse an archive-created symlink.
        for target, link in links:
            if Path(link).is_absolute() or not (target.parent / link).resolve().is_relative_to(destination.resolve()):
                raise ValueError(f"Unsafe archive link: {link}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(link)


def unpack(archive: Path, destination: Path) -> Path:
    if (destination / ".complete").is_file():
        return destination
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as temporary:
        staged = Path(temporary) / "content"
        staged.mkdir()
        extract_archive(archive, staged)
        (staged / ".complete").write_text("ready\n")
        try:
            staged.rename(destination)
        except OSError:
            # Concurrent first use may have installed the same immutable bundle.
            if not (destination / ".complete").is_file():
                raise
    return destination


def ensure_shared() -> Path:
    archive = SKILL / "assets/shared.zip"
    if not archive.is_file():
        raise RuntimeError("Missing assets/shared.zip; install the complete specula-lite skill directory")
    return unpack(archive, cache_dir() / f"shared-{sha256(archive)}")


def java_works(executable: str) -> bool:
    try:
        result = subprocess.run([executable, "-version"], capture_output=True, text=True, timeout=15)
    except (OSError, subprocess.TimeoutExpired):
        return False
    version = re.search(r'version\s+"(\d+)', result.stdout + result.stderr)
    return result.returncode == 0 and version is not None and int(version.group(1)) >= 21


def ensure_java() -> str:
    override = os.environ.get("SPECULA_LITE_JAVA")
    if override:
        if not java_works(override):
            raise RuntimeError(f"SPECULA_LITE_JAVA is not a working Java 21+: {override}")
        return str(Path(override).resolve())
    candidates = []
    executable = "java.exe" if os.name == "nt" else "java"
    if os.environ.get("JAVA_HOME"):
        candidates.append(str(Path(os.environ["JAVA_HOME"]) / "bin" / executable))
    system_java = shutil.which("java")
    if system_java:
        candidates.append(system_java)
    for candidate in candidates:
        if java_works(candidate):
            return str(Path(candidate).resolve())
    system = {"Linux": "linux", "Darwin": "mac", "Windows": "windows"}.get(platform.system())
    machine = platform.machine().lower()
    architecture = {"x86_64": "x64", "amd64": "x64", "aarch64": "aarch64", "arm64": "aarch64"}.get(machine)
    checksum = JAVA_HASHES.get((system, architecture))
    if checksum is None:
        raise RuntimeError("No bundled JRE for this platform; prepare Java 21+ and set SPECULA_LITE_JAVA")
    suffix = "zip" if system == "windows" else "tar.gz"
    filename = f"OpenJDK21U-jre_{architecture}_{system}_hotspot_{JAVA_RELEASE}.{suffix}"
    archive = download(f"{JAVA_BASE}/{filename}", cache_dir() / "downloads" / filename, checksum)
    root = unpack(archive, cache_dir() / f"java-{JAVA_RELEASE}-{system}-{architecture}")
    for candidate in root.rglob(executable):
        if candidate.parent.name == "bin" and java_works(str(candidate)):
            return str(candidate)
    raise RuntimeError(f"Downloaded Java could not run on this system; inspect {root}")


def prepare() -> dict[str, object]:
    shared = ensure_shared()
    java = ensure_java()
    jars = [str(download(url, cache_dir() / name, checksum)) for name, url, checksum in JARS]
    return {"java": java, "jars": jars, "shared": str(shared), "guides": str(shared / "skills")}


if __name__ == "__main__":
    try:
        print(json.dumps(prepare(), indent=2))
    except (OSError, RuntimeError, ValueError, tarfile.TarError, zipfile.BadZipFile) as error:
        print(f"Specula Lite preparation failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
