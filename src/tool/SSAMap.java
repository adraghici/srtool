package tool;

import java.util.HashMap;
import java.util.Map;

public class SSAMap {
    private static final Integer DEFAULT_ID = 0;
    private final Map<String, Integer> nextID;

    public SSAMap() {
        this.nextID = new HashMap<>();
    }

    public SSAMap(Map<String, Integer> nextID) {
        this.nextID = nextID;
    }

    public int id(String var) {
        if (nextID.containsKey(var)) {
            return nextID.get(var);
        }
        return DEFAULT_ID;
    }

    public int fresh(String var) {
        return id(var) + 1;
    }

    public void update(String var, int id) {
        nextID.put(var, id);
    }

    @Override
    public SSAMap clone() {
        Map<String, Integer> nextIDCopy = new HashMap<>();
        for (String s : nextID.keySet()) {
            nextIDCopy.put(s, nextID.get(s));
        }

        return new SSAMap(nextIDCopy);
    }
}
