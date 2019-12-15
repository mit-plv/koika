#!/usr/bin/env bash

css_url=https://cdn.rawgit.com/matthiaseisen/docutils-css/master/docutils_basic.css
css_extra='tt.literal { background-color: inherit; }'
rst2html.py --stylesheet=<(wget -qO- "$css_url"; echo "$css_extra") README.rst README.html

archive="koika-$(git rev-parse --short HEAD).tar.gz"
rm -f "$archive"
{ printf "README.html\0"; git ls-files -z; } | grep --null-data -v '^package.sh$' | \
    tar --create --gzip --file "$archive" --transform "s,^,koika/," --null --files-from=-
