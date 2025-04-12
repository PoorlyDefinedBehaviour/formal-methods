### TODO

- [ ] Drop messages with a view lower than the current view
- [ ] Perfom state transfer when replica receives a message from a replica with a higher view, then process the message
- [ ] Only process messages where the message view matches the current view