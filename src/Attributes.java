import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class Attributes implements Set<Character> {
    private final HashSet<Character> attributes = new HashSet<>();

    public boolean addAttributes(Character ch) {
        return this.attributes.add(ch);
    }

    public HashSet<Character> getAttributes() {
        return attributes;
    }

    public int length() {
        int counter = 0;
        for(Character c: attributes) {
            counter++;
        }

        return counter;
    }

    @Override
    public int size() {
        return attributes.size();
    }

    public boolean isEmpty() {
        return attributes.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return attributes.contains((Character) o);
    }

    @Override
    public Iterator<Character> iterator() {
        return attributes.iterator();
    }

    @Override
    public Object[] toArray() {
        return attributes.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        // TODO: 17-03-2023  
        return (T[]) attributes.toArray();
    }

    @Override
    public boolean add(Character character) {
        return attributes.add(character);
    }

    @Override
    public boolean remove(Object o) {
        return attributes.remove(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return attributes.containsAll(c);
    }

    @Override
    public boolean addAll(Collection<? extends Character> c) {
        return attributes.addAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return attributes.retainAll(c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return attributes.removeAll(c);
    }

    @Override
    public void clear() {
        attributes.clear();
    }
}
