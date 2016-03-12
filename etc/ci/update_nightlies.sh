#!/bin/bash

PS4='$ '
set -x

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
cd "$ROOT_DIR"

# only make if we should ($UPDATE_NIGHTLIES is not empty) and we're the same as origin/master
if [ -z "$UPDATE_NIGHTLIES" ]; then
    echo 'Not updating nightlies because $UPDATE_NIGHTLIES is not set'
    exit 0
fi

git reset --hard || exit 1

"$DIR"/add_upstream.sh || exit 1

git remote update || exit 1

SUPPORTS_UNSHALLOW="$(git fetch --help | grep -c -- '--unshallow')"
if [ "$SUPPORTS_UNSHALLOW" -eq 0 ]; then
    echo "Your git ($(git --version)) does not support the --unshallow option to fetch"
    git fetch --depth 1000000000 || exit 1
else
    git fetch --unshallow
fi

git fetch --tags || exit 1

PDFS="lob.pdf lob-preprint.pdf"

"$DIR"/configure_commit.sh || exit 1
git remote -v
git branch -a
git --no-pager diff HEAD
git --no-pager diff HEAD..origin/master
git --no-pager diff HEAD..upstream/master
ls

BAD_REMOTES="$(git remote -v | grep origin | grep -v 'github.com/JasonGross/lob-paper')"
UPSTREAM_LOG="$(git log HEAD..upstream/master)"
#MASTER_LOG="$(git log HEAD..master)"
#ORIGIN_LOG="$(git log HEAD..origin/master)"

MASTER_COMMIT="$(git rev-parse HEAD)"

git checkout -b gh-pages upstream/gh-pages || exit 1

git rm -rf nightly || true
rm -rf nightly || true

mkdir nightly

git add -f $PDFS || exit 1

git mv $PDFS nightly/ || exit 1

git rm -rf nightly/html

git add -f html || exit 1

git mv -f html nightly/ || exit 1

git commit -m "Update nightly builds (auto)" || exit 1
NIGHTLY_COMMIT="$(git rev-parse HEAD)"

git --no-pager diff HEAD
git --no-pager diff HEAD..origin/gh-pages
git --no-pager diff HEAD..upstream/gh-pages

# check that we're in the right place, or that we have -f
if [ "$1" != "-f" ]; then
    if [ ! -z "$BAD_REMOTES" ]; then
	echo 'Not updating nightlies because there are remotes which are not JasonGross/masters-thesis:'
	echo "$BAD_REMOTES"
	exit 0
    fi

    # only make the nightlies if we're the same as upstream/master
    if [ ! -z "$UPSTREAM_LOG" ]; then
	echo "Not making nightlies beause we do not match with upstream/master; call '$0 -f' to force"
	exit 0
    fi

#    # only make the nightlies if we're the same as master
#    if [ ! -z "$MASTER_LOG" ]; then
#	echo "Not making nightlies beause we do not match with master; call '$0 -f' to force"
#	exit 0
#    fi
#
#    # only make the nightlies if we're the same as upstream/master
#    if [ ! -z "$ORIGIN_LOG" ]; then
#	echo "Not making nightlies beause we do not match with origin/master; call '$0 -f' to force"
#	exit 0
#    fi
fi

git reset --hard || exit 1

git checkout "$MASTER_COMMIT"

"$DIR"/checkout-and-cherry-pick-and-push.sh upstream/gh-pages "$NIGHTLY_COMMIT" gh-pages || exit 1

popd 1>/dev/null
