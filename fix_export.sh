#!/usr/bin/env sh
perl -i -pe 's/^(Hint|Instance)/#[export]$1/' $@
