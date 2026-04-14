{{- define "admission.fullname" -}}
{{- default "admission-controller" .Values.nameOverride | trunc 63 | trimSuffix "-" -}}
{{- end -}}

{{- define "admission.labels" -}}
app.kubernetes.io/name: admission
app.kubernetes.io/instance: {{ .Release.Name }}
{{- end -}}

{{- define "admission.selectorLabels" -}}
app.kubernetes.io/name: admission
app.kubernetes.io/instance: {{ .Release.Name }}
{{- end -}}
