## Dafny Installation Instructions

### Mac

If you are on Mac, [Homework 0](https://github.com/DavisPL-Teaching/189c-hw0) had the correct instructions:
  ```
  brew install dotnet
  brew install dafny
  ```
  Then, in VSCode, install the Dafny extension -- link here:
  https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode

## On GitHub Codespaces, Windows, or Linux

There are two steps:
install the VSCode extension, then add
dafny to your path.

1. In VSCode, install the Dafny extension (link above).
Open up a Dafny file and wait for the extension to prompt
you to confirm installing Dafny 4.6.0.

  **Linux only:** Before running the VSCode extension, you may need to
run `sudo apt install dotnet-sdk-6.0` to make sure dotnet is installed.

  **Codespaces only:** If you're getting an "unable to connect" error when
  opening the codespace, try switching browsers - I have been
  encountering this error in Firefox, but not on Safari.

  Make sure that the green checkmarks are showing up in VSCode before
continuing!

2. Once the green checkmarks show up, that means Dafny is installed,
so you are 90% of the way there! The remaining part is just to
tell your terminal where `dafny` is on your system.
To do that, you need to add `dafny` to your PATH.

  The easiest way to find the path to Dafny is by looking at
  the output when Dafny is installed in VSCode, you should see
  a line in the output like this:
  ```
  extracting Dafny to /home/codespace/.vscode-remote/extensions/dafny-lang.ide-vscode-3.3.0/out/resources/4.6.0/github
  ```
  Copy the above path and add `/dafny` at the end, and run the
  following command (on Windows, this only works in WSL or a linux-style
  shell):
  ```
  export PATH=$PATH:/home/vscode/.vscode-remote/extensions/dafny-lang.ide-vscode-3.3.0/out/resources/4.6.0/github/dafny
  ```

  You can also call the dafny executable directly,
  it's `<path above>/dafny` or `<path>\Dafny.exe` on Windows.
  For example on Windows you can just use:
  ```
  C:\Users\user_name\.vscode\extensions\dafny-lang.ide-vscode-3.3.0\out\resources\3.10.0\github\dafny\Dafny.exe --version
  ```

  That's it!
  Now `dafny` should work from the command line -- see
  "Checking that installation worked" below.

## Additional ways to get the PATH: (optional)

The easiest way to get the PATH is by checking the dafny output
when the extension is first installed (see above).
However, if you want to find the path to Dafny directly with a
command, here's how you can do that:

On Linux or Codespaces: run this:
```
find /home -type d -name dafny
```

The output should be something like
```
/home/codespace/.vscode-remote/extensions/dafny-lang.ide-vscode-3.3.0/out/resources/4.6.0/github/dafny
```

which you can add to your path directly:
```
export PATH=$PATH:/home/vscode/.vscode-remote/extensions/dafny-lang.ide-vscode-3.3.0/out/resources/4.6.0/github/dafny
```

On Windows, I recommend using WSL or another linux-style shell
so that the above commands work.
The default terminal in VScode is Powershell.
Although Powershell is not recommended, you can also get the path
and run dafny from Powershell:
```
Get-ChildItem C:\Users\<username> -Recurse | Where-Object { $_.Name -like "Dafny.exe" }
```
Output example:
```
C:\Users\user_name\.vscode\extensions\dafny-lang.ide-vscode-3.3.0\out\resources\3.10.0\github\dafny\Dafny.exe
```

That's where your `Dafny.exe` is! You can use it by specifying
the full path or add it to your PATH first.

## Checking that installation worked

Check that the green checkmarks are showing up on the side in VSCode.
If they are not, you may need to refresh the file or restart VSCode.

For the command line, run `dafny --version` (or `<full_path>\Dafny.exe --version` on Windows), you should get something like:
```
4.6.0
```
or:
```
4.6.0+7c82175da631d3fdc3acea92a3614d66a3fdf7f2
```
You can also run `dafny run file.dfy` on a particular file `file.dfy`
and Dafny should verify and run the file.

If the green checkmarks work but the command line doesn't, that probably means you haven't added Dafny to your PATH yet
(see the Windows/Codespaces instructions).

## Troubleshooting

If you are having any trouble after following the installation instructions above,
please let us know by making a post on Piazza and we will try to help
you! See
[this post](https://piazza.com/class/lt90i40zrot3ue/post/28)
for Piazza guidelines about posting errors.
If the instructions are not working locally on your machine,
try running Dafny in a codespace via the instructions above.
