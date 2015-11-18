package tool;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import visitor.CallVisitor;
import visitor.LoopUnwindingVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;

import java.io.IOException;
import java.util.List;

public class BMC implements VerificationStrategy {
    private Program program;
    private final ConstraintSolver solver;
    private final List<String> programStates;
    private final CandidateAssertCollector candidateAssertCollector;
    private final ImmutableList<Visitor> mutatingVisitors;

    public BMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        programStates = Lists.newArrayList();
        candidateAssertCollector = new CandidateAssertCollector();
        mutatingVisitors = ImmutableList.of(
            new ShadowingVisitor(),
            new CallVisitor(candidateAssertCollector),
            new LoopUnwindingVisitor(),
            new ReturnVisitor(candidateAssertCollector));
    }

    @Override
    public String run() throws IOException, InterruptedException {
        mutatingVisitors.forEach(visitor -> {
            program = (Program) visitor.visit(program);
            programStates.add(program.toString(visitor));
        });

        SMTModel smtModel = new SMTGenerator(program).generateSMT();
        String smtCode = smtModel.getCode();
        programStates.add(smtModel.getCode());

        return solver.run(smtCode).getDecision();
    }

    @Override
    public String toString() {
        return String.join("\n", programStates);
    }
}
