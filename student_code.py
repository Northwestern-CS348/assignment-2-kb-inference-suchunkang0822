import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        # Check and see if fact_or_rule is a Fact
        if isinstance(fact_or_rule,Fact):
            # and if fact_and_rule is in the kb,
            if fact_or_rule in self.facts:
                # use _get_fact method to replace fact_or_rule
                # with the one existing in kb to pass it on to the
                # helper function
                fact_or_rule = self._get_fact(fact_or_rule)
                self.retract_helper(fact_or_rule)


    # helper function to the kb_retract.
    def retract_helper(self,fact_or_rule):
        # Check if fact_or_rule is a Fact.
        if isinstance(fact_or_rule,Fact):
            # If the fact_or_rule is supported to begin with,
            # set fac_or_rule.asserted to False since it is supported.
            if len(fact_or_rule.supported_by) > 0:
                fact_or_rule.asserted = False;
            # If the fact_or_rule is unsupported, go
            # through the list of other facts it supports by going through
            # its 'supports_facts'.Then from a fact from its 'supports_facts', go through the 'supported_by'
            # and see if it contains fact_or_rule, which needs to be removed.
            # If so, remove that whole element from 'supported_by' which contains fact_or_rule.
            # Apply same procedures to the 'supported_by_rule' as well.
            # Do so by recursively in order to go through every facts and rules that are associated with fact_or_rule.
            # After all of the associations with fact_or_rule is wiped clean, then delete fact_or_rule
            # from the kb.
            elif len(fact_or_rule.supported_by) == 0:
                for f in fact_or_rule.supports_facts:
                    for fr in f.supported_by:
                        if fact_or_rule in fr:
                            f.supported_by.remove(fr)
                    self.retract_helper(f)
                for r in fact_or_rule.supports_rules:
                    for fr in r.suppored_by:
                        if fact_or_rule in fr:
                            r.suppored_by.remove(fr)
                    self.retract_helper(r)
                self.facts.remove(fact_or_rule)

        # If the fact_or_rule is asserted, you can't delete it. If not, check
        # if it is supported. If not go through the same procedure as above.
        if isinstance(fact_or_rule,Rule):
            if not fact_or_rule.asserted:
                if len(fact_or_rule.supported_by) > 0:
                    fact_or_rule.asserted = False;
                elif len(fact_or_rule.supported_by) == 0:
                    for f in fact_or_rule.supports_facts:
                        for fr in f.supported_by:
                            if fact_or_rule in fr:
                                f.supported_by.remove(fr)
                        self.retract_helper(f)
                    for r in fact_or_rule.supports_rules:
                        for fr in r.suppored_by:
                            if fact_or_rule in fr:
                                r.suppored_by.remove(fr)
                        self.retract_helper(r)
                    self.rules.remove(fact_or_rule)






        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        #Student code goes here

        #First see if given fact and the first element of the lhs matches
        bindings = match(fact.statement,rule.lhs[0])
        if bindings:
            # if lhs has only one statement bind rhs with the bindings from fact
            # to produce corresponding statement and lhs then construct supported_by
            # list of the fact and the rule then append new_fact to supports_fact field of
            # the rule and the fact and to the existing kb
            if len(rule.lhs) == 1:
                new_statement = instantiate(rule.rhs,bindings);
                new_fact = Fact(new_statement,[[fact,rule]]);
                kb.kb_add(new_fact);
                fact.supports_facts.append(new_fact);
                rule.supports_facts.append(new_fact);
            # if lhs has more than one statements excluding the first element of lhs,
            # produce corresponding statements for the rest of the lhs. Then construct a
            # new rule and lastly add new_rule to the kb,fact,and the rule.
            elif len(rule.lhs) > 1:
                rhs_statement = instantiate(rule.rhs,bindings);
                lhs_statement = [];
                for element in rule.lhs[1:]:
                    lhs_statement.append(instantiate(element,bindings))
                new_rule = Rule([lhs_statement,rhs_statement],[[fact,rule]]);
                kb.kb_add(new_rule);
                fact.supports_rules.append(new_rule);
                rule.supports_rules.append(new_rule);







