# TLA examples for the conference session _Debugging Designs—Beyond the Rubber Duck_ held at Vincit Non-conference 2022

Copyright 2022 Erkki Seppälä <erkki.seppala@vincit.fi> and Jarno Malmari <jarno.malmari@vincit.fi>

# License

This repository is licensed [under the MIT license](LICENSE.MIT).

# Examples

## [DieHard](DieHard)

The DieHard example is copied from
https://github.com/tlaplus/Examples/ and is licensed under the [MIT
license](https://github.com/tlaplus/Examples/blob/master/LICENSE.md).

## [BallDrop](BallDrop)

A simple example of a scenario involving a ball, a table, and a couch.

## [HelloWorld](HelloWorld)

Demonstrates how to construct a set of two words using just three
words!

## [Increment](Increment)

An example about concurrent processes with PlusCal, with a bug when
accessing the same variable from multiple threads without locking.

## [DirectoryDownload](DirectoryDownload)

Aka "Enterprise directory downloader". An example where a client
mirrors the contents of one directory on a remote server. Client and
server and user interface exchange messages via a Channel, while the
top-level Main module binds all the modules together.

To generate state diagram with [tlsd](https://github.com/eras/tlsd):

```
tlc Main.tla -config tlsd.cfg | python3 -m tlsd
```
