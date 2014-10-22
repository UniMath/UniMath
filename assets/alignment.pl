use strict;
use warnings;
use List::Util ('first');

my $in_table = 0;
my $indent = "";
my @columns = ();

while (my $line = <>) {
	if ($line =~ / {2,}/) {
		chomp ($line);
		if (!$in_table) {
			print "<table>\n";
			$in_table = 1;
			$line =~ /((?:&nbsp;)*)/;
			$indent = $1;
			@columns = ();
		}

		my $cols = $line;
		utf8::decode ($cols);
		$cols =~ s/^$indent//g;
		$cols =~ s/^( *)/"_" x length ($1)/eg;
		$line =~ s/^$indent((?:&nbsp;)*)/"$indent" . (" " x length ($1))/eg;
		$cols =~ s/<(([^">]*)|"[^"]*")*>//g;
		$cols =~ s/(?:&nbsp;)/ /g;
		$cols =~ s/&[^;]*;/_/g;
		my $init_columns = !@columns;
		my $next_index = 0;
		while ($cols =~ /( {2,})/) {
			my $column = length ($`) + length ($1);
			my $replace_by = "";
			my $index = $#columns;
			if ($init_columns) {
				push (@columns, $column);
			} else {
				$index = first { $columns[$_] == $column } 0..$#columns;
				if (!defined ($index)) {
					print STDERR "Invalid alignment in $ARGV, line $. (could not find column at index $column in " . join(", ", @columns) . ").\n";
					utf8::encode ($cols);
					print STDERR "==> $cols\n";
					utf8::decode ($cols);
					$index = $next_index;
				}
				while ($next_index < $index) {
					$replace_by .= "</td><td>";
					$next_index += 1;
				}
				$next_index += 1;
			}
			$cols =~ s/( {2,})/"_" x length ($1)/e;
			if ($cols =~ / {2,}/ or $index == $#columns) {
				$replace_by .= "</td><td>";
			} else {
				$replace_by .= "</td><td colspan=\"" . ($#columns - $index + 1) . "\">";
			}
			$line =~ s/ {2,}/$replace_by/;
		}

		$line =~ s/ {2,}/<\/td><td>/g;
		print "<tr><td>$line</td></tr>\n";
	} elsif ($in_table) {
		print "</table>\n";
		print $line;
		$in_table = 0;
	} else {
		print $line;
	}
	close ARGV if eof;
}
