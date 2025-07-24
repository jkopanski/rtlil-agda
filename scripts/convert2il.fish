#! /usr/bin/env fish

set -l validate_file '!test -f "$_flag_value"; or begin echo "Input file: $_flag_value doesn\'t exist"; exit 1; end'
set -l options (fish_opt --short=i --long-only --long=input --required-val)$validate_file
set options $options (fish_opt --short=o --long-only --long=output --long-only --required-val)
set options $options (fish_opt --short=h --long=help)

set -g program (basename (status basename))

argparse $options -- $argv
or exit 1

function usage
    echo -n "Usage: $program [OPTION]

Convert hdl (Verilog) into RTLIL.

Available options:

      --input=FILE           FILE with the design to convert
      --output=FILE          FILE to store RTLIL representation
  -h, --help      display this help and exit
"
  exit
end

set -ql _flag_help
and usage

test -z $_flag_input;
and begin
    echo "Option --input=FILE is required"
    exit 1
end

test -z $_flag_output
or set -l output --outfile $_flag_output

yosys --quiet -Q -T --frontend verilog --backend rtlil $_flag_input $output
