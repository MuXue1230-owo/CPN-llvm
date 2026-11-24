; Sparse lifetime registrations for Core's native x86-64 target.
; Fields: list link, root, parent, address, original type, current type,
; initial generation, current generation, destructor, capacity, alignment,
; parent's generation at birth and a destruction-in-progress flag.
%cpn.slot = type { ptr, ptr, ptr, ptr, ptr, ptr, i64, i64, ptr, i64, i64, i64, i1 }
%cpn.reconstruction = type { ptr, ptr }
; Previous request, extent slot and birth, result address, reservation,
; required capacity and alignment, admission state, owning request, enclosing
; projection, and a preparation callback with its captured operands.
%cpn.deferred.result = type { ptr, ptr, i64, ptr, ptr, i64, i64, i1, ptr, ptr, ptr, ptr }
@cpn.slots = internal thread_local global ptr null
@cpn.epoch = internal thread_local global i64 1
@cpn.reconstructions = internal thread_local global ptr null
@cpn.deferred.results = internal thread_local global ptr null
declare ptr @malloc(i64)
declare void @free(ptr)
declare void @llvm.trap()

define internal i64 @cpn.new.generation() {
  %gen = load i64, ptr @cpn.epoch
  %next = add i64 %gen, 2
  %overflow = icmp ult i64 %next, %gen
  br i1 %overflow, label %exhausted, label %done
exhausted:
  call void @llvm.trap()
  unreachable
done:
  store i64 %next, ptr @cpn.epoch
  ret i64 %gen
}

define internal i64 @cpn.generation(ptr %slot, i1 %original) {
  %absent = icmp eq ptr %slot, null
  br i1 %absent, label %none, label %present
none:
  ret i64 0
present:
  %birth = getelementptr %cpn.slot, ptr %slot, i32 0, i32 6
  %stamp = getelementptr %cpn.slot, ptr %slot, i32 0, i32 7
  %field = select i1 %original, ptr %birth, ptr %stamp
  %value = load i64, ptr %field
  ret i64 %value
}

define internal void @cpn.slot.begin(ptr %s, ptr %addr, ptr %ty, ptr %drop, i64 %size, i64 %align, ptr %parent, i64 %parentgen) {
  %hasparent = icmp ne ptr %parent, null
  br i1 %hasparent, label %child, label %init
child:
  %ownerp = getelementptr %cpn.slot, ptr %parent, i32 0, i32 1
  %owner = load ptr, ptr %ownerp
  br label %init
init:
  %root = phi ptr [ %s, %0 ], [ %owner, %child ]
  %gen = call i64 @cpn.new.generation()
  %root.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 1
  store ptr %root, ptr %root.slot
  %parent.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 2
  store ptr %parent, ptr %parent.slot
  %address.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 3
  store ptr %addr, ptr %address.slot
  %original.type.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 4
  store ptr %ty, ptr %original.type.slot
  %current.type.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 5
  store ptr %ty, ptr %current.type.slot
  %birth.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 6
  store i64 %gen, ptr %birth.slot
  %generation.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 7
  store i64 %gen, ptr %generation.slot
  %destructor.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 8
  store ptr %drop, ptr %destructor.slot
  %capacity.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 9
  store i64 %size, ptr %capacity.slot
  %alignment.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 10
  store i64 %align, ptr %alignment.slot
  %parent.generation.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 11
  store i64 %parentgen, ptr %parent.generation.slot
  %busy = getelementptr %cpn.slot, ptr %s, i32 0, i32 12
  store i1 false, ptr %busy
  ret void
}

define internal void @cpn.slot.link(ptr %s) {
  %next = load ptr, ptr @cpn.slots
  store ptr %next, ptr %s
  store ptr %s, ptr @cpn.slots
  ret void
}

define internal ptr @cpn.slot.find(ptr %addr, ptr %ty, ptr %parent, i1 %checkparent) {
  %head = load ptr, ptr @cpn.slots
  br label %scan
scan:
  %s = phi ptr [ %head, %0 ], [ %next, %advance ]
  %empty = icmp eq ptr %s, null
  br i1 %empty, label %done, label %test
test:
  %ap = getelementptr %cpn.slot, ptr %s, i32 0, i32 3
  %a = load ptr, ptr %ap
  %sameaddr = icmp eq ptr %a, %addr
  %tp = getelementptr %cpn.slot, ptr %s, i32 0, i32 4
  %t = load ptr, ptr %tp
  %original = icmp eq ptr %t, %ty
  %cp = getelementptr %cpn.slot, ptr %s, i32 0, i32 5
  %c = load ptr, ptr %cp
  %current = icmp eq ptr %c, %ty
  %either = or i1 %current, %original
  %pp = getelementptr %cpn.slot, ptr %s, i32 0, i32 2
  %p = load ptr, ptr %pp
  %sameparent = icmp eq ptr %p, %parent
  %child = and i1 %original, %sameparent
  %matchtype = select i1 %checkparent, i1 %child, i1 %either
  %match = and i1 %sameaddr, %matchtype
  br i1 %match, label %done, label %advance
advance:
  %next = load ptr, ptr %s
  br label %scan
done:
  ret ptr %s
}

define internal ptr @cpn.slot.child(ptr %parent, ptr %addr, ptr %ty, ptr %drop, i64 %size, i64 %align) {
  %missing = icmp eq ptr %parent, null
  br i1 %missing, label %none, label %lookup
none:
  ret ptr null
lookup:
  %parentgen = call i64 @cpn.generation(ptr %parent, i1 false)
  %found = call ptr @cpn.slot.find(ptr %addr, ptr %ty, ptr %parent, i1 true)
  %fresh = icmp eq ptr %found, null
  br i1 %fresh, label %allocate, label %test
test:
  %gp = getelementptr %cpn.slot, ptr %found, i32 0, i32 11
  %old = load i64, ptr %gp
  %same = icmp eq i64 %old, %parentgen
  br i1 %same, label %keep, label %init
keep:
  ret ptr %found
allocate:
  %mem = call ptr @malloc(i64 ptrtoint (ptr getelementptr (%cpn.slot, ptr null, i32 1) to i64))
  %oom = icmp eq ptr %mem, null
  br i1 %oom, label %failed, label %link
failed:
  call void @llvm.trap()
  unreachable
link:
  call void @cpn.slot.link(ptr %mem)
  br label %init
init:
  %s = phi ptr [ %found, %test ], [ %mem, %link ]
  call void @cpn.slot.begin(ptr %s, ptr %addr, ptr %ty, ptr %drop, i64 %size, i64 %align, ptr %parent, i64 %parentgen)
  ret ptr %s
}

; End all dependent views, including descendants that were abandoned.
define internal void @cpn.slot.invalidate(ptr %s) {
  %stamp = getelementptr %cpn.slot, ptr %s, i32 0, i32 7
  %value = load i64, ptr %stamp
  %ended = and i64 %value, -2
  store i64 %ended, ptr %stamp
  %head = load ptr, ptr @cpn.slots
  br label %scan
scan:
  %n = phi ptr [%head, %0], [%next, %advance]
  %done = icmp eq ptr %n, null
  br i1 %done, label %end, label %test
test:
  %pp = getelementptr %cpn.slot, ptr %n, i32 0, i32 2
  %parent = load ptr, ptr %pp
  %child = icmp eq ptr %parent, %s
  br i1 %child, label %invalidate, label %advance
invalidate:
  call void @cpn.slot.invalidate(ptr %n)
  br label %advance
advance:
  %next = load ptr, ptr %n
  br label %scan
end:
  ret void
}

; A pending reconstruction belongs to its storage registration until commit
; or rollback. Search only pending operations and their containing extents.
define internal i1 @cpn.slot.constructing(ptr %extent) {
entry:
  %head = load ptr, ptr @cpn.reconstructions
  br label %scan
scan:
  %entry.slot = phi ptr [ %head, %entry ], [ %next, %advance ]
  %empty = icmp eq ptr %entry.slot, null
  br i1 %empty, label %absent, label %lookup
lookup:
  %storage = getelementptr %cpn.reconstruction, ptr %entry.slot, i32 0, i32 1
  %registered = load ptr, ptr %storage
  br label %ancestry
ancestry:
  %slot = phi ptr [ %registered, %lookup ], [ %parent, %up ]
  %same = icmp eq ptr %slot, %extent
  br i1 %same, label %found, label %up
up:
  %link = getelementptr %cpn.slot, ptr %slot, i32 0, i32 2
  %parent = load ptr, ptr %link
  %root = icmp eq ptr %parent, null
  br i1 %root, label %advance, label %ancestry
advance:
  %next = load ptr, ptr %entry.slot
  br label %scan
found:
  ret i1 true
absent:
  ret i1 false
}

define internal i1 @cpn.slot.reserve(ptr %entry, ptr %slot) {
  %occupied = call i1 @cpn.slot.constructing(ptr %slot)
  br i1 %occupied, label %blocked, label %commit
blocked:
  ret i1 false
commit:
  %previous = load ptr, ptr @cpn.reconstructions
  store ptr %previous, ptr %entry
  %storage = getelementptr %cpn.reconstruction, ptr %entry, i32 0, i32 1
  store ptr %slot, ptr %storage
  store ptr %entry, ptr @cpn.reconstructions
  ret i1 true
}

define internal void @cpn.slot.unreserve(ptr %entry) {
  %head = load ptr, ptr @cpn.reconstructions
  %active = icmp eq ptr %head, %entry
  br i1 %active, label %remove, label %done
remove:
  %previous = load ptr, ptr %entry
  store ptr %previous, ptr @cpn.reconstructions
  br label %done
done:
  ret void
}

define internal i1 @cpn.slot.admit.replacement(ptr %slot, i64 %birth, ptr %reservation, i64 %size, i64 %align) {
  %present = call i1 @cpn.extent.valid(ptr %slot, i64 %birth)
  br i1 %present, label %extent, label %rejected
extent:
  %generation = call i64 @cpn.generation(ptr %slot, i1 false)
  %live = trunc i64 %generation to i1
  %capacity.field = getelementptr %cpn.slot, ptr %slot, i32 0, i32 9
  %alignment.field = getelementptr %cpn.slot, ptr %slot, i32 0, i32 10
  %capacity = load i64, ptr %capacity.field
  %alignment = load i64, ptr %alignment.field
  %small = icmp ult i64 %capacity, %size
  %misaligned = icmp ult i64 %alignment, %align
  %unavailable = or i1 %live, %small
  %invalid = or i1 %unavailable, %misaligned
  br i1 %invalid, label %rejected, label %reserve
reserve:
  %reserved = call i1 @cpn.slot.reserve(ptr %reservation, ptr %slot)
  ret i1 %reserved
rejected:
  ret i1 false
}

define internal void @cpn.slot.link.result(ptr %entry, ptr %result, ptr %owner, ptr %enclosing, ptr %prepare, ptr %state) {
  %previous = load ptr, ptr @cpn.deferred.results
  store ptr %previous, ptr %entry
  %result.field = getelementptr %cpn.deferred.result, ptr %entry, i32 0, i32 3
  %owner.field = getelementptr %cpn.deferred.result, ptr %entry, i32 0, i32 8
  %enclosing.field = getelementptr %cpn.deferred.result, ptr %entry, i32 0, i32 9
  %prepare.field = getelementptr %cpn.deferred.result, ptr %entry, i32 0, i32 10
  %state.field = getelementptr %cpn.deferred.result, ptr %entry, i32 0, i32 11
  store ptr %result, ptr %result.field
  store ptr %owner, ptr %owner.field
  store ptr %enclosing, ptr %enclosing.field
  store ptr %prepare, ptr %prepare.field
  store ptr %state, ptr %state.field
  store ptr %entry, ptr @cpn.deferred.results
  ret void
}

define internal void @cpn.slot.defer.result(ptr %request, ptr %slot, i64 %birth, ptr %result, ptr %reservation, i64 %size, i64 %align, ptr %prepare, ptr %state) {
  %slot.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 1
  %birth.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 2
  %reservation.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 4
  %size.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 5
  %align.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 6
  %admitted.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 7
  store ptr %slot, ptr %slot.field
  store i64 %birth, ptr %birth.field
  store ptr %reservation, ptr %reservation.field
  store i64 %size, ptr %size.field
  store i64 %align, ptr %align.field
  store i1 false, ptr %admitted.field
  call void @cpn.slot.link.result(ptr %request, ptr %result, ptr %request, ptr null, ptr %prepare, ptr %state)
  ret void
}

define internal ptr @cpn.slot.find.result(ptr %result) {
entry:
  %head = load ptr, ptr @cpn.deferred.results
  br label %scan
scan:
  %request = phi ptr [ %head, %entry ], [ %previous, %advance ]
  %ordinary = icmp eq ptr %request, null
  br i1 %ordinary, label %missing, label %match
match:
  %result.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 3
  %destination = load ptr, ptr %result.field
  %same = icmp eq ptr %destination, %result
  br i1 %same, label %found, label %advance
advance:
  %previous = load ptr, ptr %request
  br label %scan
found:
  ret ptr %request
missing:
  ret ptr null
}

; A projected field and the returned object share one admission and reservation.
define internal void @cpn.slot.project.result(ptr %projection, ptr %enclosing, ptr %result, ptr %prepare, ptr %state) {
entry:
  %parent = call ptr @cpn.slot.find.result(ptr %enclosing)
  %ordinary = icmp eq ptr %parent, null
  br i1 %ordinary, label %ordinary.result, label %link
link:
  %owner.field = getelementptr %cpn.deferred.result, ptr %parent, i32 0, i32 8
  %owner = load ptr, ptr %owner.field
  call void @cpn.slot.link.result(ptr %projection, ptr %result, ptr %owner, ptr %parent, ptr %prepare, ptr %state)
  ret void
ordinary.result:
  %has.prefix = icmp ne ptr %prepare, null
  br i1 %has.prefix, label %initialize, label %done
initialize:
  call void %prepare(ptr %state)
  br label %done
done:
  ret void
}

; Finish the enclosing initialized prefix before constructing the field.
define internal void @cpn.slot.prepare.result(ptr %projection) {
entry:
  %parent.field = getelementptr %cpn.deferred.result, ptr %projection, i32 0, i32 9
  %parent = load ptr, ptr %parent.field
  %has.parent = icmp ne ptr %parent, null
  br i1 %has.parent, label %outer, label %read
outer:
  call void @cpn.slot.prepare.result(ptr %parent)
  br label %read
read:
  %prepare.field = getelementptr %cpn.deferred.result, ptr %projection, i32 0, i32 10
  %prepare = load ptr, ptr %prepare.field
  %has.prefix = icmp ne ptr %prepare, null
  br i1 %has.prefix, label %initialize, label %done
initialize:
  %state.field = getelementptr %cpn.deferred.result, ptr %projection, i32 0, i32 11
  %state = load ptr, ptr %state.field
  store ptr null, ptr %prepare.field
  call void %prepare(ptr %state)
  br label %done
done:
  ret void
}

define internal i1 @cpn.slot.admit.result(ptr %result) {
entry:
  %projection = call ptr @cpn.slot.find.result(ptr %result)
  %ordinary = icmp eq ptr %projection, null
  br i1 %ordinary, label %admitted, label %read
read:
  %owner.field = getelementptr %cpn.deferred.result, ptr %projection, i32 0, i32 8
  %request = load ptr, ptr %owner.field
  %admitted.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 7
  %ready = load i1, ptr %admitted.field
  br i1 %ready, label %prepare, label %validate
validate:
  %slot.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 1
  %birth.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 2
  %reservation.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 4
  %size.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 5
  %align.field = getelementptr %cpn.deferred.result, ptr %request, i32 0, i32 6
  %slot = load ptr, ptr %slot.field
  %birth = load i64, ptr %birth.field
  %reservation = load ptr, ptr %reservation.field
  %size = load i64, ptr %size.field
  %align = load i64, ptr %align.field
  %valid = call i1 @cpn.slot.admit.replacement(ptr %slot, i64 %birth, ptr %reservation, i64 %size, i64 %align)
  br i1 %valid, label %commit, label %rejected
commit:
  store i1 true, ptr %admitted.field
  br label %prepare
prepare:
  call void @cpn.slot.prepare.result(ptr %projection)
  br label %admitted
admitted:
  ret i1 true
rejected:
  ret i1 false
}

define internal void @cpn.slot.end.result(ptr %request) {
entry:
  %head = load ptr, ptr @cpn.deferred.results
  %active = icmp eq ptr %head, %request
  br i1 %active, label %remove, label %done
remove:
  %previous = load ptr, ptr %request
  store ptr %previous, ptr @cpn.deferred.results
  br label %done
done:
  ret void
}

define internal void @cpn.slot.retire(ptr %s, i1 %destroy) {
  %generation = call i64 @cpn.generation(ptr %s, i1 false)
  %live = trunc i64 %generation to i1
  br i1 %live, label %begin, label %done
begin:
  %busy = getelementptr %cpn.slot, ptr %s, i32 0, i32 12
  %running = load i1, ptr %busy
  br i1 %running, label %done, label %check
check:
  %constructing = call i1 @cpn.slot.constructing(ptr %s)
  br i1 %constructing, label %blocked, label %end
blocked:
  call void @llvm.trap()
  unreachable
end:
  store i1 true, ptr %busy
  %dp = getelementptr %cpn.slot, ptr %s, i32 0, i32 8
  %drop = load ptr, ptr %dp
  %hasdrop = icmp ne ptr %drop, null
  %run = and i1 %hasdrop, %destroy
  br i1 %run, label %call, label %invalidate
call:
  %ap = getelementptr %cpn.slot, ptr %s, i32 0, i32 3
  %addr = load ptr, ptr %ap
  call void %drop(ptr %addr)
  br label %invalidate
invalidate:
  call void @cpn.slot.invalidate(ptr %s)
  store i1 false, ptr %busy
  br label %done
done:
  ret void
}

; Root records live on their activation's stack. Free sparse child records
; only when the owning extent ends, so stale views can still be checked.
define internal void @cpn.slot.release(ptr %root) {
  br label %scan
scan:
  %link = phi ptr [@cpn.slots, %0], [%link, %unlink], [%link, %free], [%s, %keep]
  %s = load ptr, ptr %link
  %empty = icmp eq ptr %s, null
  br i1 %empty, label %done, label %test
test:
  %rp = getelementptr %cpn.slot, ptr %s, i32 0, i32 1
  %owner = load ptr, ptr %rp
  %match = icmp eq ptr %root, %owner
  br i1 %match, label %unlink, label %keep
keep:
  br label %scan
unlink:
  %next = load ptr, ptr %s
  store ptr %next, ptr %link
  %stack = icmp eq ptr %s, %root
  br i1 %stack, label %scan, label %free
free:
  call void @free(ptr %s)
  br label %scan
done:
  ret void
}

; A borrowed registration can outlive its owner's stack frame or sparse entry.
; Compare its identity against linked records before inspecting its contents.
define internal i1 @cpn.slot.linked(ptr %wanted) {
  %head = load ptr, ptr @cpn.slots
  br label %scan
scan:
  %s = phi ptr [%head,%0], [%next,%advance]
  %empty = icmp eq ptr %s, null
  br i1 %empty, label %absent, label %test
test:
  %same = icmp eq ptr %s, %wanted
  br i1 %same, label %found, label %advance
advance:
  %next = load ptr, ptr %s
  br label %scan
found:
  ret i1 true
absent:
  ret i1 false
}

define internal i1 @cpn.borrow.valid(ptr %slot, i64 %expected) {
  %raw = icmp eq ptr %slot, null
  br i1 %raw, label %valid, label %member
member:
  %linked = call i1 @cpn.slot.linked(ptr %slot)
  br i1 %linked, label %test, label %expired
test:
  %stamp = call i64 @cpn.generation(ptr %slot, i1 false)
  %original = call i64 @cpn.generation(ptr %slot, i1 true)
  %implicit = icmp eq i64 %expected, 0
  %want = select i1 %implicit, i64 %original, i64 %expected
  %same = icmp eq i64 %want, %stamp
  %alive = trunc i64 %stamp to i1
  %ok = and i1 %same, %alive
  ret i1 %ok
valid:
  ret i1 true
expired:
  ret i1 false
}

; A child extent belongs to one generation of its containing object.
define internal i1 @cpn.extent.valid(ptr %slot, i64 %extentid) {
  %linked = call i1 @cpn.slot.linked(ptr %slot)
  br i1 %linked, label %first, label %invalid
first:
  %birthid = call i64 @cpn.generation(ptr %slot, i1 true)
  %same = icmp eq i64 %birthid, %extentid
  br i1 %same, label %scan, label %invalid
scan:
  %s = phi ptr [%slot, %first], [%p, %test]
  %pp = getelementptr %cpn.slot, ptr %s, i32 0, i32 2
  %p = load ptr, ptr %pp
  %root = icmp eq ptr %p, null
  br i1 %root, label %valid, label %test
test:
  %bp = getelementptr %cpn.slot, ptr %s, i32 0, i32 11
  %birth = load i64, ptr %bp
  %actual = call i64 @cpn.generation(ptr %p, i1 false)
  %live = trunc i64 %actual to i1
  %matches = icmp eq i64 %actual, %birth
  %ok = and i1 %matches, %live
  br i1 %ok, label %scan, label %invalid
valid:
  ret i1 true
invalid:
  ret i1 false
}
