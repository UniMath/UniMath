#!/usr/bin/env bash

# Check the code style of the UniMath project
# Auke Booij, 2017

#
# START helper functions
#

die() {
        echo "$@" >&2
        exit 1
}

check_grep() {
    typeset cmd="grep --color=always -E -A4 -B4 -n $1 $2"
    typeset ret_code

    output=$($cmd)
    ret_code=$?

    if [ $ret_code != 0 ] && [ $ret_code != 1 ]
    then
        die "Failed to run command:" "$cmd"
    fi

    if [[ ! -z $output ]]
    then
        (( FAILURES++ ))
        echo "$output"
    fi

}

check_command() {
    check_grep "^[[:space:]]*($2)(\.|[^a-zA-Z][^.]*?\.)" "$1"
}

check_type() {
    check_grep "[^[:space:]a-zA-Z.][^a-zA-Z.]+($2)($|[^a-zA-Z_])" "$1"
}

check_tactic() {
    check_grep "(^|\.|;)[[:space:]]*($2)[^.;]*(\.|;)" "$1"
}

check_freestanding() {
    check_grep "[^[:space:]](.*[^a-zA-Z]|)($2)\." "$1"
}

check_line_length() {
    check_grep "^.{101}" "$1"
}

check_line_start() {
    check_grep "^[[:space:]]*:=?" "$1"
}

check_file() {

    echo "Checking style of $1..."
    # Do not use Admitted or introduce new axioms.
    check_command "$1" "Admitted"
    # Do not use Inductive or Record, except in Foundations/Basics/Preamble.v.
    if [[ $1 != *"Foundations/Basics/Preamble.v" ]]
    then
        check_command "$1" "Inductive|Record"
    fi
    # Do not use Module or Structure.
    # Do not use Fixpoint.
    check_command "$1" "Structure|Fixpoint"
    if [[ $1 != *"Tests.v" ]]
    then
        check_command "$1" "Module"
    fi
    # Do not use Prop or Set, and ensure definitions don't produce
    # elements of them.
    check_type "$1" "Prop|Set"
    # Do not use Type, except in Foundations/Basics/Preamble.v. Use UU
    # instead. If higher universes are needed, they should be added to
    # Foundations/Basics/Preamble.v
    if [[ $1 != *"Foundations/Basics/Preamble.v" ]]
    then
        check_type "$1" "Type"
    fi
    # Do not use destruct, match, case, square brackets with intros,
    # or nested square brackets with induction. (The goal is to
    # prevent generation of proof terms using match.)
    #
    # Use do with a specific numerical count, rather than repeat, to
    # make proofs easier to repair.
    check_tactic "$1" "destruct|match|case|intros[^.;]*\[|induction[^.;]*\[[^].;]*\[|repeat"
    # Start all proofs with Proof. on a separate line and end it with
    # Defined. on a separate line, as this makes it possible for us to
    # generate HTML with expansible/collapsible proofs.
    check_freestanding "$1" "Proof|Defined"
    # Each line should be limited to at most 100 (unicode) characters.
    check_line_length "$1"
    # Within the core Foundations package:
    #    Do not start lines with : or with :=.
    if [[ $1 == *"/Foundations/"* ]]
    then
        check_line_start "$1"
    fi
}

#
# END helper functions
#

#
# START subcommand functions
#

cmd_check_files() {
    echo "Checking $# files for code style..."
    echo
    for file in "$@"
    do
        check_file "$file"
    done
}

cmd_all() {
    cmd_check_files $(grep -E "^UniMath/" ./.coq_makefile_input)
}

#
# END subcommand functions
#

PROGRAM="${0##*/}"
COMMAND="$1"
FAILURES=0

case "$1" in
        --all) shift;                   cmd_all ;;
        *)                              cmd_check_files "$@" ;;
esac
exit 0


# Do not use Admitted or introduce new axioms.
# Do not use apply with a term that needs no additional arguments filled in, because using exact would be clearer.
# Do not use Prop or Set, and ensure definitions don't produce elements of them.
# Do not use Type, except in Foundations/Basics/Preamble.v. Use UU instead. If higher universes are needed, they should be added to Foundations/Basics/Preamble.v.
# Do not use Inductive or Record, except in Foundations/Basics/Preamble.v.
# Do not use Module or Structure.
# Do not use Fixpoint.
# Do not use destruct, match, case, square brackets with intros, or nested square brackets with induction. (The goal is to prevent generation of proof terms using match.)
# Use do with a specific numerical count, rather than repeat, to make proofs easier to repair.
# Use as to name all new variables introduced by induction or destruct, if the corresponding type is defined in a remote location, because different names might be used by Coq when the definition of the type is changed. Name all variables introduced by assert, if they are used by name later, with as or to the left of a colon.
# Do not end a proof with Qed., except with Goal, for that may prevent later computations.
# Start all proofs with Proof. on a separate line and end it with Defined. on a separate line, as this makes it possible for us to generate HTML with expansible/collapsible proofs.
# Use Unicode notation freely, but make the parsing conventions uniform across files, and consider putting them into a scope.
# Each line should be limited to at most 100 (unicode) characters. The makefile target enforce-max-line-length can be used to detect nonconforming files, and the target show-long-lines can be used to display the nonconforming lines.
# Always use Coq's proof structuring syntax ( { } + - * ) to focus on a single goal immediately after a tactic creates additional goals.
# Indentation should normally be that produced automatically by emacs' coq-mode.
# Within the core Foundations package:
#     Do not start lines with : or with :=.
#     One should normally put an extra blank line between units. Exceptions may be made for closely related items.
# When using abstract in a proof, it is unsound to refer later by name to the abstracted lemma (whose name typically ends with _subproof), because its type may vary from one version of Coq to another. Coq's current behavior is also unlikely to be duplicated precisely by a future proof assistant.
