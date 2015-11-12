package ssa;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class Scope {
    private final IdMap idMap;
    private String pred;
    private Map<String, Integer> ids;

    private Scope(IdMap idMap, String pred, String ass) {
        this.idMap = idMap;
        this.pred = pred;
        this.ids = new HashMap<>();
    }

    public static Scope create(IdMap idMap) {
        return new Scope(idMap, "", "");
    }

    public static Scope fromScope(Scope scope) {
        Scope copy = create(scope.idMap);
        copy.pred = scope.pred;
        copy.ids = new HashMap<>(scope.ids);
        return copy;
    }

    public static Scope fromScope(Scope scope, String pred) {
        Scope copy = create(scope.idMap);
        copy.pred = pred;
        copy.ids = new HashMap<>(scope.ids);
        return copy;
    }

    public String getPred() {
        return pred;
    }

    public void declareVar(String var) {
        updateVar(var, idMap.fresh(var));
    }

    public boolean hasVar(String var) {
        return ids.containsKey(var);
    }

    public int getId(String var) {
        if (!ids.containsKey(var)) {
            updateVar(var, idMap.fresh(var));
        }
        return ids.get(var);
    }

    /**
     * Increases the id of the given variable from the fresh id provider and returns the new id.
     */
    public int increaseVar(String var) {
        int id = idMap.fresh(var);
        updateVar(var, id);
        return id;
    }

    public void updateVar(String var, int id) {
        ids.put(var, id);
    }

    public Set<String> vars() {
        return ids.keySet();
    }
}
