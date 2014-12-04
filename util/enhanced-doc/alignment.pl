# Copyright (c) 2014, Guillaume Verdier <guillaume@verdier.info>
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# 1. Redistributions of source code must retain the above copyright notice, this
#    list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright notice,
#    this list of conditions and the following disclaimer in the documentation
#    and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
# ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use strict;
use warnings;
use List::Util ('first');

my @all_cols = ();
my @columns;
my $in_align = 0;

while (my $line = <>) {
	chomp($line);
	utf8::decode($line);

	if (!$in_align) {
		if (start_align($line)) {
			$in_align = 1;
			@all_cols = ();
		} else {
			utf8::encode($line);
			print "$line\n";
			next;
		}
	} elsif (end_align($line)) {
		print_align();
		$in_align = 0;
		utf8::encode($line);
		print "$line\n";
		next;
	}

	my @cols = split(/(  +)/, $line);

	my %line_cols = ();
	my $first_col = shift(@cols);
	$first_col =~ /^((?:&nbsp;)*)/;
	my $indent = length($1) / 6;
	$line_cols{$indent} = $first_col;

	my $offset = length(normalize($first_col));
	for (my $index = 1; $index <= $#cols; $index += 2) {
		$offset += length($cols[$index - 1]);
		my $col = $cols[$index];
		$line_cols{$offset} = $col;
		$offset += length(normalize($col));
	}

	push(@all_cols, \%line_cols);
	@columns = get_all_columns(@all_cols);
}
print_align() if $in_align;

sub start_align {
	return $_[0] =~ /  /;
}

sub end_align {
	my ($line) = @_;

	return 0 if ($line =~ /  /);

	$line =~ /^((?:&nbsp;)*)/;
	my $indent = length($1) / 6;

	my $index = first { $columns[$_] == $indent } 1..$#columns;
	return 0 if defined($index);

	return 1;
}

sub normalize {
	$_ = shift;
	s/&[^;]*;/_/g;
	s/<([^">]|("[^"]*"))*>//g;
	return $_;
}

sub print_align {
	print "<table class=\"alignment\">\n";
	for my $cols (@all_cols) {
		print "\t<tr>";
		my $index = 0;
		while ($index <= $#columns) {
			my $col = $cols->{$columns[$index]};
			$col = "" unless defined($col);
			$col =~ s/(&nbsp;)*// if $index > 0;
			$col =~ s/<br\/?>//;
			$index += 1;
			my $colspan = 1;
			while ($index <= $#columns && !defined($cols->{$columns[$index]})) {
				$colspan += 1;
				$index += 1;
			}
			utf8::encode($col);
			print "<td colspan=\"$colspan\">$col&nbsp;</td>";
		}
		print "</tr>\n";
	}
	print "</table>\n";
}

sub get_all_columns {
	my (@cols) = @_;
	my @res = ();
	push(@res, keys(%$_)) for (@cols);
	my %h = map {$_, 1} @res;
	return sort {$a <=> $b} keys %h;
}
