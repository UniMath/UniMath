all : to_upstream_files.vo pretowers.vo towers.vo

to_upstream_files.vo : to_upstream_files.v
	coqc "-indices-matter" "-no-sharing" "-R" "/Users/VV/Dropbox/Documents/Coq/UniMath/UniMath/" "UniMath" to_upstream_files

pretowers.vo : pretowers.v to_upstream_files.vo
	coqc "-indices-matter" "-no-sharing" "-R" "/Users/VV/Dropbox/Documents/Coq/UniMath/UniMath/" "UniMath" pretowers

towers.vo : towers.v to_upstream_files.vo
	coqc "-indices-matter" "-no-sharing" "-R" "/Users/VV/Dropbox/Documents/Coq/UniMath/UniMath/" "UniMath" towers
