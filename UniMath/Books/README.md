# Books

UniMath is a vast library. This package is a navigational and organizational aid,
its aim is to establish correspondences between the results in UniMath and those
presented in some familiar textbooks.

The names serve as a guide only, they are not intended to be referenced in other
proof scripts.

## Style

Every file should `Require` (not `Import`!) the definitions from UniMath to be
referenced, and use `Local Definition` to add a name, referring to it by
qualified path.

The aim of these guidelines is to aid in consistency and readability, while
avoiding name clashes.

## Contributing

Contributions are very welcome! These files are quite lightweight and don't add
a significant maintenance burden. Even if there is already a book on e.g. group
theory represented in this package, we still welcome contributions of other
books on the same subject.
