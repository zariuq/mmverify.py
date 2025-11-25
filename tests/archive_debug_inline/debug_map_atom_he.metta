!(println! "What does map-atom see in (term (t + r))?")
!(map-atom (term (t + r)) $tok (println! $tok))
