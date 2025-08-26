# Chandy-Lamport

[Distributed Algorithms - Chapter 3.1](https://www.amazon.com/dp/0262037661)

This spec simulates a banking system receiving transfers between accounts. Any snapshot should follow the rules of
Chandy-Lamport. Snapshots should capture account state and transfers in flight. The sum of all account states and
transfers in flight should be constant for all snapshots.

- https://github.com/tlaplus/DrTLAPlus/tree/master/GSnapshot
- https://www.youtube.com/watch?v=ao58xine3jM
- https://lamport.azurewebsites.net/pubs/chandy.pdf

## TODO

- Add support for [alternate peer topologies](https://www.youtube.com/watch?v=ao58xine3jM&t=42m)
