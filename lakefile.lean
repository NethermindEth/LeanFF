import Lake

open System Lake DSL

package ff where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.22.0-rc2"

@[default_target]
lean_lib FF

def OSXarmName := "cvc5-FF-macOS-arm64-static-gpl"
def OSXx86Name := "cvc5-FF-macOS-x86_64-static-gpl"
def LinuxarmName := "cvc5-FF-Linux-arm64-static-gpl"
def Linuxx86Name := "cvc5-FF-Linux-x86_64-static-gpl"
def WinName := "UNSUPPORTED"

def OSXarmUri := s!"https://github.com/NethermindEth/cvc5_smff_lean/releases/download/latest/{OSXarmName}-2025-10-15-7368f1d.zip"
def OSXx86Uri := s!"https://github.com/NethermindEth/cvc5_smff_lean/releases/download/latest/{OSXx86Name}-2025-10-15-7368f1d.zip"
def LinuxarmUri := s!"https://github.com/NethermindEth/cvc5_smff_lean/releases/download/latest/{LinuxarmName}-2025-10-15-7368f1d.zip"
def Linuxx86Uri := s!"https://github.com/NethermindEth/cvc5_smff_lean/releases/download/latest/{Linuxx86Name}-2025-10-15-7368f1d.zip"
def WinUri := s!"https://github.com/NethermindEth/cvc5_smff_lean/releases/download/latest/{WinName}-2025-10-15-7368f1d.zip"

def cvc5root := "cvc5ff"

inductive Platform where | OSXarm | OSXx86 | Win | Linuxarm | Linuxx86

namespace Platform

/-
Windows is currently unsupported.
-/

def toDirBase : Platform → String
  | .OSXarm => OSXarmName
  | .OSXx86 => OSXx86Name
  | .Linuxarm => LinuxarmName
  | .Linuxx86 => Linuxx86Name
  | .Win => WinName

def toUri : Platform → String
  | .OSXarm => OSXarmUri
  | .OSXx86 => OSXx86Uri
  | .Linuxarm => LinuxarmUri
  | .Linuxx86 => Linuxx86Uri
  | .Win => WinUri

def downloadCmd : Platform → IO.Process.SpawnArgs
  -- `-L - follow redirect`
  | platform => {cmd := "curl", args := #["-L", "-o", s!"{platform.toDirBase}.zip", platform.toUri]}

def unzipCmd : Platform → IO.Process.SpawnArgs
  | platform => {cmd := "unzip", args := #[s!"{platform.toDirBase}"]}

def rmzipCmd : Platform → IO.Process.SpawnArgs
  | platform => {cmd := "rm", args := #["-r", s!"{platform.toDirBase}.zip"]}

def renameCmd : Platform → IO.Process.SpawnArgs
  | platform => {cmd := "mv", args := #[s!"{platform.toDirBase}", cvc5root]}

end Platform

@[default_target]
target getCvc5 pkg : Unit := do
  let binDir := pkg.dir / ".lake" / "build" / "bin"
  IO.FS.createDirAll binDir
  let platform ← getPlatform
  if platform matches .Win then IO.println "Windows unsupported."; throw default
  if (←FilePath.readDir binDir).any (·.fileName == cvc5root) then return pure ()
  logInfo s!"Retrieving cvc5: {platform.toUri}"
  Job.async (caption := "download cvc5")
    for cmd in [platform.downloadCmd, platform.unzipCmd, platform.rmzipCmd, platform.renameCmd] do
      executeWithCwd binDir cmd
  /-
  Based on https://github.com/leanprover-community/mathlib4/blob/c092d56cb78afb6fa43d053920a22ed131e4d035/Cache/IO.lean#L241
  -/
  where
    getPlatform : IO Platform := do
      if System.Platform.isWindows
      then pure .Win
      else let arch ← (·.stdout.trim) <$> IO.Process.output {cmd := "uname", args := #["-m"]}
           match arch with
           | "arm64" => if System.Platform.isOSX then pure .OSXarm else pure .Linuxarm
           | "x86_64" => if System.Platform.isOSX then pure .OSXx86 else pure .Linuxx86
           | _ => throw <| IO.userError s!"unsupported architecture {arch}"
    executeWithCwd (cwd : System.FilePath) (cmd : IO.Process.SpawnArgs) : IO Unit :=
      discard <| IO.Process.run {cmd with cwd := cwd}
