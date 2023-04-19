#!/usr/bin/env perl6
constant @files := 'unscoped', 'axioms', 'fintype';

sub MAIN (
    Str $autosubst-dir #= the git directory of autosubst2
) {
  my IO::Path $header-dir := $autosubst-dir.IO.add("headers");
  for @files <<~>> '.v' {
      if (copy $header-dir.add($_), $_) {
          my $file := $_.IO;
          $file.chmod(0o666 +& $file.mode);
      }
      else {
           say "Failed to copy {$_}";
      }
  }
}
