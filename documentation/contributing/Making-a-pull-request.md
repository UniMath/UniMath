# Making a Pull Request

Code contributions to UniMath are made through pull requests. This guide will walk you through the process of making a pull request. The overall steps are:

1. Fork the repository
2. Clone your forked repository
3. Add the main repository as an upstream remote
4. Create a branch for your changes
5. Commit and push your changes to your fork
6. Make a pull request
7. Merge the pull request

You should check the [Contributing](./Contributing.md) instructions before doing step 6.

## Fork the repository

Forking the UniMath creates copy under your GitHub account. To do this, click the "Fork" button on the top right of the repository page. You can reuse this fork for all of your pull requests.

## Clone your forked repository

```bash
git clone https://github.com/<your-username>/UniMath.git
```
You may have already cloned the main repository. If so, you can clone your fork under a different name:
```bash
git clone https://github.com/<your-username>/UniMath.git UniMath-fork
```

## Add the main repository as an upstream remote

You may need to merge new changes from the master branch of the main repository into your fork (i.e. if they occur while you are working on your pull request). To do this, you can add the main repository as an upstream remote. Here we are giving it the name `upstream`.

```bash
cd UniMath # your fork
git remote add upstream https://github.com/UniMath/UniMath.git
# Check your current remotes
git remote -v
```
To merge new changes from the main repository into your fork, checkout the branch you want to merge into, then run:
```bash
git fetch upstream
git merge upstream/master # merge the master branch into the current checked-out branch
```

## Create a branch for your changes

You may work on one or more contributions at once by isolating your changes to a *branch*.
Choose a name appropriate for your changes, e.g. `YonedaLemma`, and create it:

```bash
# Create a new branch and switch to it ('check it out')
git checkout -b YonedaLemma
# View branches and see which is currently checked out
git branch
# To go back to the master branch
git checkout master
# And back to the contribution branch
git checkout YonedaLemma
```

### Resources
- [Git - Basic Branching and Merging](https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging)

## Commit and push your changes to your fork

With your contribution branch checked out, you can make changes to the code. As you make changes you can commit them to your local repository, and then push them to your fork.

```bash
# Stage all changes
git add -A
# Commit the changes
git commit -m "what I did"
# Push the changes to your fork
git push -u origin YonedaLemma
```

> [!NOTE]
> The `-u` flag tells git to set the upstream branch for the branch `YonedaLemma`. This means that in the future you can just run `git push` while `YonedaLemma` is checked-out to push more committed changes to your fork.

### Resources
- [Git - Recording Changes to the Repository](https://git-scm.com/book/en/v2/Git-Basics-Recording-Changes-to-the-Repository)
- [Git - Working with Remotes](https://git-scm.com/book/en/v2/Git-Basics-Working-with-Remotes)

## Make a pull request

Before making a pull request:
- Check all your modified code compiles
- Run the sanity checks with `make sanity-checks`
- Check you have followed the [style guide](Style-Guide.md) and other instructions in [Contributing](Contributing.md) for creating new files/packages.

It is fine if there are still issues when you make the pull request. The pull request will be reviewed and you can make changes before the pull request is merged.

To make your pull request, follow this guide: [Creating a pull request from a fork](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/creating-a-pull-request-from-a-fork).

You can continue commiting and pushing changes to your fork's branch as you had been, and these will appear in the pull request.

## Merge the pull request

Once your pull request has been reviewed and approved, it can be merged. This will add your changes to the main repository.