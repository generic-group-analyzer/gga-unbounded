#! /bin/bash

function ok_tests() {
  echo 
  echo "*******************************************************************"
  echo "Running examples and ok tests!"
  echo

  FAILED=""
  OK=""
  for file in \
              tests/ok/*.ubt \
              ; do \
    printf "File $file:"
    name="tests/ok/"$(basename -s .ubt $file)".out"
    content=$(cat $name | tr -d '\n' | tr -d ' ')
    content=$(echo $content | tr -d '\n' | tr -d ' ')
    before=$(date +%s)
    output=$(./ubt.native $file | tr -d '\n' | tr -d ' ')
    if ! $(test $content = $output); then
      FAILED="$FAILED\n  $file"
    else
      OK="$OK\n  $file"
    fi
    after=$(date +%s)
    dt=$((after - before))
    printf  " \e[1;33m$dt seconds\e[1;0m\n"
    done

  printf "\nFailed: $FAILED"
  printf "\nOK: $OK\n"
}

function fail_tests() {
  echo
  echo
  echo "*******************************************************************"
  echo "Running mustfail tests!"
  echo

  FAILED=""
  OK=""
  for file in test/fail/*.zc; do
    ERR=`grep ERROR $file | sed 's/ERROR: //'`
    printf "Testing $file, expecting error ''$ERR''\n"  
    if ! ./autognp $file 2>&1 | \
         grep -F "$ERR"; then
      FAILED="$FAILED\n  $file"
    else
      OK="$OK\n  $file"
    fi
  done
  printf "\nFailed:$FAILED"
  printf "\nOK:$OK\n"
}

ok_tests
#fail_tests
