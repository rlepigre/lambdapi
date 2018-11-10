#!/bin/bash

NBWORKERS="${NBWORKERS:-1}"

SRC="https://deducteam.github.io/data/libraries/iProverModulo_dk.tar.gz"
DIR="iprover"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -rf ${DIR}
  rm -rf iProverModulo_dk
  rm -f iProverModulo_dk.tar.gz
  if [[ "$1" = "fullclean" ]]; then
    rm -f iprover.tar.gz
  fi
  exit 0
fi

# Rejecting other command line arguments.
if [[ "$#" -ne 0 ]]; then
  echo "Invalid argument, usage: $0 [clean | fullclean]"
  exit -1
fi

# Checking for the "lambadpi" command (first in LAMBDAPI).
if [[ ! -v LAMBDAPI ]]; then
  # Falling back to installed "lambdapi" command.
  LAMBDAPI="$(which lambdapi 2> /dev/null)"
  if [[ -z "${LAMBDAPI}" ]]; then
    echo "No lambdapi command found... (not in path)"
    echo "A command may be specified with the LAMBDAPI environment variable."
    exit -1
  fi
fi

# Prepare the library if necessary.
if [[ ! -d ${DIR} ]]; then
  # The directory is not ready, so we need to work.
  echo "Preparing the library:"

  # Download the library if necessary.
  if [[ ! -f iprover.tar.gz ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC} -O iprover.tar.gz
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  tar xf iprover.tar.gz
  mv iProverModulo_dk ${DIR}
  echo "OK"

  # Applying the changes (add "#REQUIRE hol" and fix obsolete syntax).
  echo -n "  - applying changes... "
  sed -i "s/^#NAME FOL.//g" "${DIR}/FOL.dk"
  for SIG in `find ${DIR} -type f -name "*_sig.dk"`; do
    MSIG=`basename "${SIG}" ".dk"`
    PRF="${SIG%%_sig.dk}_prf.dk"
    sed -i "s/^#NAME [a-zA-Z0-9_]\+./#REQUIRE FOL./g" ${SIG}
    sed -i "s/^#NAME [a-zA-Z0-9_]\+./#REQUIRE FOL.\n#REQUIRE ${MSIG}./g" ${PRF}
  done
  echo "OK"

  # Blacklist.
  rm ${DIR}/SYN865d1_prf.dk
  rm ${DIR}/NLP004p1_prf.dk
  rm ${DIR}/SYN843d1_prf.dk
  rm ${DIR}/HWV107d1_prf.dk
  rm ${DIR}/SYN893d1_prf.dk
  rm ${DIR}/SYN869d1_prf.dk
  rm ${DIR}/SYN871d1_prf.dk
  rm ${DIR}/KRS155p1_prf.dk
  rm ${DIR}/SYN900d1_prf.dk
  rm ${DIR}/SYN846d1_prf.dk
  rm ${DIR}/HWV014d1_prf.dk
  rm ${DIR}/NLP117d1_prf.dk
  rm ${DIR}/SYN837d1_prf.dk
  rm ${DIR}/SWV816d1_prf.dk
  rm ${DIR}/SYN898d1_prf.dk
  rm ${DIR}/LCL764d1_prf.dk
  rm ${DIR}/HWV019d3_prf.dk
  rm ${DIR}/HWV015d2_prf.dk
  rm ${DIR}/HWV013d1_prf.dk
  rm ${DIR}/NLP122p1_prf.dk
  rm ${DIR}/SYN858d1_prf.dk
  rm ${DIR}/NLP001p1_prf.dk
  rm ${DIR}/HWV025d2_prf.dk
  rm ${DIR}/NLP009d1_prf.dk
  rm ${DIR}/SYN862d1_prf.dk
  rm ${DIR}/ALG376d1_prf.dk
  rm ${DIR}/HWV014d2_prf.dk
  rm ${DIR}/NLP001d1_prf.dk
  rm ${DIR}/SYN857d1_prf.dk
  rm ${DIR}/KRS159p1_prf.dk
  rm ${DIR}/SYN844d1_prf.dk
  rm ${DIR}/KRS151p1_prf.dk
  rm ${DIR}/SYN859d1_prf.dk
  rm ${DIR}/NLP009p1_prf.dk
  rm ${DIR}/HWV025d3_prf.dk
  rm ${DIR}/HWV009d4_prf.dk
  rm ${DIR}/SYN875d1_prf.dk
  rm ${DIR}/HWV026d2_prf.dk
  rm ${DIR}/SYN861d1_prf.dk
  rm ${DIR}/SYN899d1_prf.dk
  rm ${DIR}/SYN879d1_prf.dk
  rm ${DIR}/LCL787d1_prf.dk
  rm ${DIR}/SYN887d1_prf.dk
  rm ${DIR}/HWV009d2_prf.dk
  rm ${DIR}/HWV027d2_prf.dk
  rm ${DIR}/SYN833d1_prf.dk
  rm ${DIR}/SYN856d1_prf.dk
  rm ${DIR}/SYN891d1_prf.dk
  rm ${DIR}/HWV024d1_prf.dk
  rm ${DIR}/SYN849d1_prf.dk
  rm ${DIR}/HWV021d1_prf.dk
  rm ${DIR}/SYN848d1_prf.dk
  rm ${DIR}/KRS153p1_prf.dk
  rm ${DIR}/SYN890d1_prf.dk
  rm ${DIR}/NLP094p1_prf.dk
  rm ${DIR}/SWV827d1_prf.dk
  rm ${DIR}/SYN860d1_prf.dk
  rm ${DIR}/HWV019d2_prf.dk
  rm ${DIR}/SYN895d1_prf.dk
  rm ${DIR}/SYN845d1_prf.dk
  rm ${DIR}/PUZ017d1_prf.dk
  rm ${DIR}/SWV789d1_prf.dk
  rm ${DIR}/SYN873d1_prf.dk
  rm ${DIR}/SYN886d1_prf.dk
  rm ${DIR}/SWV836d1_prf.dk
  rm ${DIR}/HWV025d1_prf.dk
  rm ${DIR}/SYN883d1_prf.dk
  rm ${DIR}/SWV839d1_prf.dk
  rm ${DIR}/ALG375d1_prf.dk
  rm ${DIR}/HWV012d1_prf.dk
  rm ${DIR}/SYN897d1_prf.dk
  rm ${DIR}/SYN813d1_prf.dk
  rm ${DIR}/NLP081d1_prf.dk
  rm ${DIR}/SYN877d1_prf.dk
  rm ${DIR}/SYN901d1_prf.dk
  rm ${DIR}/NLP007p1_prf.dk
  rm ${DIR}/KRS161p1_prf.dk
  rm ${DIR}/SYN836d1_prf.dk
  rm ${DIR}/NLP011d1_prf.dk
  rm ${DIR}/NLP122d1_prf.dk
  rm ${DIR}/HWV009d3_prf.dk
  rm ${DIR}/HWV019d1_prf.dk
  rm ${DIR}/SWV826d1_prf.dk
  rm ${DIR}/SYN834d1_prf.dk
  rm ${DIR}/SWV844d1_prf.dk
  rm ${DIR}/SYN885d1_prf.dk
  rm ${DIR}/SYN896d1_prf.dk
  rm ${DIR}/SYN889d1_prf.dk
  rm ${DIR}/SYN882d1_prf.dk
  rm ${DIR}/NLP079d1_prf.dk
  rm ${DIR}/SYN881d1_prf.dk
  rm ${DIR}/SYN866d1_prf.dk
  rm ${DIR}/SWV092p1_prf.dk
  rm ${DIR}/HWV027d1_prf.dk
  rm ${DIR}/SWW210p1_prf.dk
  rm ${DIR}/NLP007d1_prf.dk
  rm ${DIR}/SYN876d1_prf.dk
  rm ${DIR}/SYN880d1_prf.dk
  rm ${DIR}/NLP080d1_prf.dk
  rm ${DIR}/SWV811d1_prf.dk
  rm ${DIR}/NLP004d1_prf.dk
  rm ${DIR}/SWV794d1_prf.dk
  rm ${DIR}/NLP094d1_prf.dk
  rm ${DIR}/HWV026d1_prf.dk
  rm ${DIR}/SWW219p1_prf.dk
  rm ${DIR}/SYN892d1_prf.dk
  rm ${DIR}/KRS162p1_prf.dk
  rm ${DIR}/NLP117p1_prf.dk
  rm ${DIR}/SYN820d1_prf.dk
  rm ${DIR}/SWW225p1_prf.dk
  rm ${DIR}/SCT007d1_prf.dk
  rm ${DIR}/HWV012d2_prf.dk
  rm ${DIR}/SYN847d1_prf.dk
  rm ${DIR}/SYN894d1_prf.dk
  rm ${DIR}/HWV021d2_prf.dk
  rm ${DIR}/SWV611d1_prf.dk
  rm ${DIR}/HWV015d1_prf.dk
  rm ${DIR}/HWV026d3_prf.dk
  rm ${DIR}/NLP011p1_prf.dk
  rm ${DIR}/KRS147p1_prf.dk
  rm ${DIR}/SWW221p1_prf.dk
  rm ${DIR}/SYN884d1_prf.dk
  rm ${DIR}/SWV620d1_prf.dk
  rm ${DIR}/SYN878d1_prf.dk
  rm ${DIR}/SYN850d1_prf.dk
  rm ${DIR}/HWV013d2_prf.dk
  rm ${DIR}/SYN874d1_prf.dk
  rm ${DIR}/SYN819d1_prf.dk

  # Cleaning up.
  echo -n "  - cleaning up...      "
  rm ${DIR}/Makefile
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
else
  # Cleaning up build directory
  rm -f ${DIR}/*.lpo
  rm -f ${DIR}/error.log
fi

# Moving to the working directory.
cd ${DIR}

# Compiling the theory file.
${LAMBDAPI} --gen-obj FOL.dk

# Checking function.
function check() {
  # Module checking (given its name, without "_sig" or "_prf".
  function check_module() {
    SIG_FILE="$1_sig.dk"
    OBJ_FILE="$1_sig.lpo"
    PRF_FILE="$1_prf.dk"
    ${LAMBDAPI} --verbose 0 --gen-obj ${SIG_FILE}
    if [ $? -ne 0 ]; then
      echo -e "\033[0;31mKO\033[0m ${SIG_FILE}"
      echo "FAILED ${SIG_FILE}" >> error.log
    elif [ -f "${PRF_FILE}" ]; then
      echo -e "\033[0;32mOK\033[0m ${SIG_FILE}"
      ${LAMBDAPI} --verbose 0 ${PRF_FILE}
      if [ $? -ne 0 ]; then
        echo -e "\033[0;31mKO\033[0m ${PRF_FILE}"
        echo "FAILED ${PRF_FILE}" >> error.log
      else
        echo -e "\033[0;32mOK\033[0m ${PRF_FILE}"
      fi
      rm ${OBJ_FILE}
    else
      echo -e "\033[0;33mBL\033[0m ${SIG_FILE}"
      echo "BLACK LISTED ${PRF_FILE}" >> error.log
    fi
  }

  # Export things for the module checking function.
  export readonly LAMBDAPI=${LAMBDAPI}
  export -f check_module

  # Run module check on all modules.
  find -name "*_sig.dk" | sed 's/_sig\.dk//g' \
    | xargs -P ${NBWORKERS} -n 1 -I{} bash -c "check_module {}"
}

# Export stuff for the checking function.
export readonly LAMBDAPI=${LAMBDAPI}
export readonly NBWORKERS=${NBWORKERS}
export -f check

# Run the actual checks.
\time -f "Finished in %E at %P with %MKb of RAM" bash -c "check"
