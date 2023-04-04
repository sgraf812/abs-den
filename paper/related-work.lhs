\section{Related Work}
\label{sec:related-work}

%\sg{Move to related work.}
%There have been attempts to discern crashes from other kinds of loops, such as
%\cite{imprecise-exceptions}. Unfortunately, in Section 5.3 they find it
%impossible give non-terminating programs a denotation other than $\bot$, which
%still encompasses all possible exception behaviors.
%
% eval/apply or push/enter?
% Given an expr like $f x$, we first push $ρ(x)$ onto the stack and then
% evaluate $f$, which will look it up (pushing an udpate frame) and evaluate its
% RHS. Since we will never return to the "eval site" of $f$, IMO this qualifies
% as push/enter rather than eval/apply. Which is in contrast to what the Krivine
% paper says, which dubs return states as "apply" transitions
