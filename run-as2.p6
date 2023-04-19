#!/usr/bin/env perl6
my @files := "stlc", "coc";

for @files -> $file {
    for True, False -> $well-scoped {
        my Str $output;
        my Str $opt;
        if $well-scoped {
            $output = "{$file}.v";
            $opt = "Coq";
        }
        else {
            $output = "{$file}_unscoped.v";
            $opt = "UCoq";
        }
        run 'as2-exe',
        '-p', $opt,
        '-i', "{$file}.sig",
        '-o', $output;
    }
}
