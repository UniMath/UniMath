git checkout master
git pull
git pull upstream
git merge upstream/master
git gui
make

if [ "$?" -eq 0 ]
then
    echo "Au travail"
    git checkout dev
    git pull
    git merge master
    git gui
    make
    emacs UniMath/Dedekind
    
    make -j -k && git gui
else
    echo "erreur dans la mise a jour de master"
fi
