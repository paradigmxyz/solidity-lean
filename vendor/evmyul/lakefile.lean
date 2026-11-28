import Lake
open Lake DSL System

require "leanprover-community" / "mathlib" @ git "v4.35.0"

package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

def cloneWithCache (pkg : NPackage __name__) (dirname url rev : String) : FetchM (Job GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then
    dbg_trace s!"Cloning: {url}"
    GitRepo.clone url repoDir
    repoDir.checkoutDetach rev
  return pure repoDir

target cloneSha2 pkg : GitRepo :=
  cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"
    "565f65009bdd98267361b17d50cddd7c9beb3e6c"

target cloneKeccak256 pkg : GitRepo :=
  cloneWithCache pkg "keccak256" "https://github.com/brainhub/SHA3IUF.git"
    "fc8504750a5c2174a1874094dd05e6a0d8797753"

def hash256CDir (hash256repo : GitRepo) : FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

target ffi.o pkg : FilePath := do
  let sha2 ← (←cloneSha2.fetch).await
  let keccak256 ← (←cloneKeccak256.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "EvmYul" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString,
    "-I", keccak256.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (Job FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

def buildKeccak256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneKeccak256.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256 ← buildKeccak256Obj pkg "sha3"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch

  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[sha256O, keccak256, ffiO]

lean_lib «Conform» where
  roots := #[`Conform.Wheels]

@[default_target]
lean_lib «EvmYul» where
  globs := #[.submodules `EvmYul]
