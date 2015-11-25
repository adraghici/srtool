package visitor;

import ast.CandidateInvariant;
import ast.CandidatePostcondition;
import ast.CandidatePrecondition;
import ast.Invariant;
import ast.Node;
import ast.Postcondition;
import ast.Precondition;
import tool.AssertCollector;

import java.util.Set;

/**
 * Visitor used to transform all candidate conditions (preconditions, postconditions, loop invariants) to
 * their non-candidate counterparts.
 */
public class CandidateVisitor extends DefaultVisitor {
    private final Set<Node> artificialConditions;

    public CandidateVisitor(AssertCollector assertCollector, Set<Node> artificialConditions) {
        super(assertCollector);
        this.artificialConditions = artificialConditions;
    }

    @Override
    public Precondition visit(CandidatePrecondition candidatePrecondition) {
        Precondition precondition = new Precondition(candidatePrecondition.getCondition());
        artificialConditions.add(precondition);
        assertCollector.addOrigin(precondition);
        return precondition;
    }

    @Override
    public Postcondition visit(CandidatePostcondition candidatePostcondition) {
        Postcondition postcondition = new Postcondition(candidatePostcondition.getCondition());
        artificialConditions.add(postcondition);
        assertCollector.addOrigin(postcondition);
        return postcondition;
    }

    @Override
    public Invariant visit(CandidateInvariant candidateInvariant) {
        Invariant invariant = new Invariant(candidateInvariant.getCondition());
        artificialConditions.add(invariant);
        assertCollector.addOrigin(invariant);
        return invariant;
    }

    @Override
    public String getDescription() {
        return "Candidate visitor";
    }
}
