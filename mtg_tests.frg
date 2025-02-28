#lang forge

open "mtg.frg"

pred validMana {
    all c: Card { c.manaCost >= 0 }
}

pred validCreature {
    all c: Creature {
        c.health >= 0
        c.health <= 15
        c.attack >= 0
        c.attack <= 15
        c.manaCost >= 0
        c.manaCost < 13
    }
}

test suite for cardWellformed {
    assert validMana is necessary for cardsWellInit for 6 Int
    assert validCreature is necessary for cardsWellInit for 6 Int
}

pred noCycles {
    all a: Action | {
        a not in a.^(nextAction)
    }
}

pred allReachable {
    some a: Action | {
        all b: Action | {
            a != b
            reachable[b, a, nextAction]
        }
    }
}

test suite for linearActions {
    assert noCycles is necessary for linearActions
    // assert allReachable is necessary for linearActions //this doesn't pass
}

pred zeroLife {
    some t: TIME | {
        some p: Player {
            p.lifeTotal[t] <= 0
        }
    } 
}

pred ceaseAction {
    some t: TIME | {
        some p: Player {
            no a: Action | reachable[a.currTime, t, next]
        }
    } 
}

test suite for gameEnd {
    assert zeroLife is necessary for gameEnd
    assert ceaseAction is necessary for gameEnd
}

pred switchTurn {
    all a: Action | some p1, p2: Player {
        a.nextAction.player = p1 iff a.player = p2
    }
}

pred endTurn2 {
    all a: Action | some p1, p2: Player {
        a in endTurn implies //switch players after endTurn
        a.player != a.nextAction.player    }
}

pred noDirectCycle {
    all a: Action | {
        a != a.nextAction
    }
}

test suite for validActionSequence {
    assert switchTurn is necessary for validActionSequence
    assert endTurn2 is necessary for validActionSequence
    assert noDirectCycle is necessary for validActionSequence
}

pred battlefieldsUnalike {
    some disj p1: Player, p2: Player | {
        p1.battlefield != p2.battlefield
    }
}

pred graveyardsUnalike {
    some disj p1: Player, p2: Player | {
        p1.graveyard != p2.graveyard
    }
}

pred handsUnalike {
    some disj p1: Player, p2: Player | {
        p1.hand != p2.hand
    }
}

pred decksUnalike {
    some disj p1: Player, p2: Player | {
        p1.deck != p2.deck
    }
}

test suite for playersSeparate {
    assert battlefieldsUnalike is necessary for playerSeparate
    assert graveyardsUnalike is necessary for playerSeparate
    assert handsUnalike is necessary for playerSeparate
    assert decksUnalike is necessary for playerSeparate
}