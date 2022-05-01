#!/usr/bin/env bash

function clear-ext() {
  EXT=$1
  IFS=$'\n'; set -f
  echo "Clearing *.${EXT}"
  find . -name "*.${EXT}" -exec rm {} \;
  unset IFS; set +f
}

clear-ext 'agdai'
  