#lang forge

abstract sig Boolean {}
one sig True, False extends Boolean {}

sig TIME {
    next: lone TIME
}

//Players
abstract sig Player {
    // lifeTotal: one Int
    lifeTotal: pfunc TIME -> Int,
    hand: one Hand,
    graveyard: one Graveyard,
    battlefield: one Battlefield,
    deck: one Deck
}
one sig Player1, Player2 extends Player {}

// sig Turn {
//     boardState: pfunc TIME -> BoardState
// }

// sig BoardState {
//     firstAction: one Action
//     allActions: set Action
// }

//Card Locations
abstract sig Loc {
    cards: set TIME -> Card
}
sig Hand extends Loc {}
sig Battlefield extends Loc {}
sig Graveyard extends Loc {}
sig Deck extends Loc {}

//Cards
abstract sig Card {
    tapped: one Boolean,
    manaCost: one Int
}
sig Creature extends Card {
    attack: one Int,
    health: one Int
}
sig Land extends Card {
}

abstract sig Action {
    nextAction: lone Action,
    player: one Player,
    currTime: one TIME
}
sig playCard extends Action {
    cardCast: lone Card
}
// sig castSpell extends playCard {} //for playing lands vs casting creatures

sig declareAttackers extends Action {
    attackingCreatures: set Creature
}
sig block extends Action {

}
sig endTurn extends Action {}
sig untap extends Action {}

pred separateSpaces {
    all c: Card, t: TIME, p: Player | {
        c in p.hand.cards[t] implies c not in p.battlefield.cards[t]
        implies c not in p.graveyard.cards[t]
        implies c not in p.deck.cards[t]

        c in p.battlefield.cards[t] implies c not in p.hand.cards[t]
        implies c not in p.graveyard.cards[t] 
        implies c not in p.deck.cards[t]

        c in p.graveyard.cards[t] implies c not in p.hand.cards[t] 
        implies c not in p.battlefield.cards[t] 
        implies c not in p.deck.cards[t]

        c in p.deck.cards[t] implies c not in p.hand.cards[t] 
        implies c not in p.battlefield.cards[t] 
        implies c not in p.graveyard.cards[t]
    }
}

pred playerSeparate {
    some disj p1: Player, p2: Player | {
        p1.battlefield != p2.battlefield
        p1.graveyard != p2.graveyard
        p1.hand != p2.hand
        p1.deck != p2.deck
    }
}

pred validCast {
    all c: Card, t: TIME | {
        some p: Player | {
            c in p.battlefield.cards[t] implies // if there's a card in a battlefield then it was cast validly (it was in a hand and then in the battlefield right after)
                {some castTime : TIME | {
                    castTime != t
                    reachable[t, castTime, next]
                    c in p.hand.cards[castTime]
                    c in p.battlefield.cards[castTime.next]

                    //at castTime there are enough untapped lands to afford it
                    #(p.battlefield.cards[castTime] & Land) >= c.manaCost

                    //some Action casts this card
                    {some play: playCard | {
                        play.cardCast = c
                    }}
                }}
        }
    }
}

pred cardsWellInit {
    all c: Creature | {
        c.health >= 0 //max defaults are 0-15
        c.health <= 15
        c.attack >= 0
        c.attack <= 15
        c.manaCost >= 0
        c.manaCost < 13
    }
    all l: Land | {
        l.manaCost = 0
    }
}

pred wellformedGamestart {
    some firstState: TIME | {
        all p: Player | {
            no t: TIME | t.next = firstState //no time before firstState
            p.lifeTotal[firstState] = 20 //players start with 20 life
            all b : Battlefield, g: Graveyard | #b.cards[firstState] = 0 and #g.cards[firstState] = 0 //players start with empty battlefields and graveyards
            #p.hand.cards[firstState] = 3 //players start with 3 cards in hand
            #p.deck.cards[firstState] = 2 //players start with 2 cards in deck
        }
    }
}

pred validActionSequence {
    all a: Action | some p1, p2: Player {
        a.player = p1 implies //don't switch players unless
        (a.nextAction.player = p1) or (a.nextAction.player = p2 and (a.nextAction in block or a in endTurn)) //blocking or endTurn

        a in endTurn implies //switch players after endTurn
        a.player != a.nextAction.player

        a.nextAction != a //no action can be the same as the next action
    }
}

pred gameEnd {
    some t: TIME | {
        some p: Player {
            p.lifeTotal[t] <= 0 //at some point some player should have no life (does this work???)
            no a: Action | reachable[a.currTime, t, next] //no actions after game end
        }
    } 
}

// pred turnSequence {
//     all end: endTurn | {
//         end.nextAction implies //if there's a new action after an endTurn
//         some b: BoardState | {
//             // b.firstAction in untap
//             b.firstAction = end.nextAction //that's the beginning of some new turn
//         }
//     }
// }

pred linearActions {
    all a: Action | {
        not reachable[a, a, nextAction] //actions aren't reachable from themselves (no cycles)
    }
    some firstState: Action | {
        all a: Action  | {
            (firstState != a) implies reachable[a, firstState, nextAction] //some first action from which all others reachable
        }
    }
}

pred oneCreature { //to make sure there are creatures in the runs
    all b: Battlefield | {
        some t: TIME, c: Creature | {
            c in b.cards[t]
        }
    }
}

run {cardsWellInit
    wellformedGamestart
    validActionSequence
    gameEnd
    linearActions
    separateSpaces
    validCast
    playerSeparate
    some c: Card, p: Player, t: TIME | {
        c in p.battlefield.cards[t]
    }

    //make it interesting
    oneCreature

} for exactly 10 Card, 4 Action, 2 endTurn, 8 Loc, 6 Int for {next is linear}

