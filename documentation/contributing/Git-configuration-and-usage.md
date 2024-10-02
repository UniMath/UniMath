# Merging pull requests on the commandline

Here's the way my upstream entry in .git/config looks:
```
[remote "upstream"]
url = git@github.com:UniMath/UniMath.git
fetch = +refs/heads/*:refs/remotes/upstream/*
fetch = +refs/pull/*/head:refs/remotes/upstream/pull/*
```

The final line arranges for pull requests to be fetched when you do
```git fetch --all```.  Then you get more remote branches, which are usable:
```
$ git branch -a | grep /pull/ | head
  remotes/upstream/pull/1
  remotes/upstream/pull/10
  remotes/upstream/pull/100
  remotes/upstream/pull/101
  remotes/upstream/pull/102
  remotes/upstream/pull/104
  remotes/upstream/pull/105
  remotes/upstream/pull/106
  remotes/upstream/pull/107
  remotes/upstream/pull/108
```

You can do something like ```git checkout pull/108``` and you'll have the
pull
request checked out, ready to test.  You can even merge it directly into the
upstream master branch, if you want to, and github will not get annoyed;
indeed,
it will observe the action and close the pull request.

# Links

* [Github workflow](https://guides.github.com/introduction/flow/index.html)
* [Basic merging](http://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging)
* [Merging vs. rebasing](https://www.atlassian.com/git/tutorials/merging-vs-rebasing/)
