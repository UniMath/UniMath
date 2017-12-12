
basename=UniMath

for packagename in $(ls -d ${basename}/*/); do

    rm -f ${packagename}Export.v ${packagename}Export.v.temp
    touch ${packagename}Export.v.temp
    
    for filename in $(git ls-files ${packagename}); do
	if [[ $filename == *.v ]];
	then
	    filebase=${filename%.v}
	    libname=${filebase//\//.}
	    echo "Require Export ${libname}." >> Export.v.temp
	fi
    done
    
    mv ${packagename}Export.v.temp ${packagename}Export.v
done

